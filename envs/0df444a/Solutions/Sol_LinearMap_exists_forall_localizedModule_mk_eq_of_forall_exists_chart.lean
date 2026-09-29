-- Prove2me | solution 1 for LinearMap.exists_forall_localizedModule_mk_eq_of_forall_exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c98572f4-2f29-5da4-b92c-bc3a57c09eab

import Mathlib
import Theorems.Thm_IsLocalizedModule_existsUnique_forall_comp_eq_of_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_exists_forall_localizedModule_mk_eq_of_forall_exists_chart

set_option autoImplicit false

universe u

namespace GlueStalkAux

theorem mk_mk_eq_of_forall_prime {B : Type u} [CommRing B] {T : Type u} [AddCommGroup T] [Module B T]
    (f g : B) (t t' : T) (n m : ℕ)
    (h : ∀ y : PrimeSpectrum B, f ∉ y.asIdeal → g ∉ y.asIdeal →
      ∃ u : B, u ∉ y.asIdeal ∧ u • (g ^ m • t) = u • (f ^ n • t')) :
    (LocalizedModule.mk (LocalizedModule.mk t (1 : Submonoid.powers g)) ⟨f ^ n, n, rfl⟩ :
        LocalizedModule (Submonoid.powers f) (LocalizedModule (Submonoid.powers g) T)) =
      LocalizedModule.mk (LocalizedModule.mk t' (⟨g ^ m, m, rfl⟩ : Submonoid.powers g)) 1 := by
  classical
  let δ : T := g ^ m • t - f ^ n • t'
  let I : Ideal B := (Submodule.span B {δ}).annihilator
  have hI : ∀ b : B, b ∈ I ↔ b • δ = 0 := fun b => Submodule.mem_annihilator_span_singleton δ b
  have hrad : f * g ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hIJ, hJ⟩
    by_contra hfg
    have hf : f ∉ J := fun hf => hfg (Ideal.mul_mem_right g J hf)
    have hg : g ∉ J := fun hg => hfg (Ideal.mul_mem_left J f hg)
    obtain ⟨u, hu, hut⟩ := h ⟨J, hJ⟩ hf hg
    exact hu (hIJ ((hI u).2 (by rw [smul_sub, sub_eq_zero]; exact hut)))
  obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.1 hrad
  have hkill : ((f * g) ^ N) • (g ^ m • t - f ^ n • t') = 0 := (hI _).1 hN
  have hkill' : (g ^ N * (g ^ m * f ^ N)) • t = (g ^ N * (f ^ N * f ^ n)) • t' := by
    rw [smul_sub, sub_eq_zero, mul_pow, smul_smul, smul_smul] at hkill
    rw [show g ^ N * (g ^ m * f ^ N) = f ^ N * g ^ N * g ^ m by ring,
      show g ^ N * (f ^ N * f ^ n) = f ^ N * g ^ N * f ^ n by ring]
    exact hkill
  rw [LocalizedModule.mk_eq]
  refine ⟨⟨f ^ N, N, rfl⟩, ?_⟩
  rw [one_smul, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def, LocalizedModule.smul'_mk,
    LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨⟨g ^ N, N, rfl⟩, ?_⟩
  simp only [Submonoid.smul_def, one_smul, smul_smul]
  exact hkill'

theorem exists_rep {B : Type u} [CommRing B] {T : Type u} [AddCommGroup T] [Module B T] (f : B)
    (q : LocalizedModule (Submonoid.powers f) T) : ∃ (t : T) (n : ℕ), q = LocalizedModule.mk t (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) := by
  induction q using LocalizedModule.induction_on with
  | h t s =>
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
    exact ⟨t, n, by congr 1; exact Subtype.ext hn.symm⟩

end GlueStalkAux

open GlueStalkAux in
theorem solution
    {B : Type u} [CommRing B] {T T' : Type u} [AddCommGroup T] [Module B T] [AddCommGroup T'] [Module B T']
    (φ : ∀ x : PrimeSpectrum B,
      LocalizedModule x.asIdeal.primeCompl T' →ₗ[B] LocalizedModule x.asIdeal.primeCompl T)
    (hφ : ∀ x : PrimeSpectrum B, ∃ (f : B) (_ : f ∉ x.asIdeal)
        (Φ : T' →ₗ[B] LocalizedModule (Submonoid.powers f) T),
        ∀ (y : PrimeSpectrum B), f ∉ y.asIdeal → ∀ (a : T') (t : T) (n : ℕ),
          Φ a = LocalizedModule.mk t ⟨f ^ n, Submonoid.mem_powers_iff _ _ |>.mpr ⟨n, rfl⟩⟩ →
            ∀ s : y.asIdeal.primeCompl, (s : B) = f ^ n →
              φ y (LocalizedModule.mk a 1) = LocalizedModule.mk t s) :
    ∃ τ : T' →ₗ[B] T, ∀ (x : PrimeSpectrum B) (a : T'),
      LocalizedModule.mk (τ a) 1 = φ x (LocalizedModule.mk a 1) := by
  classical
  choose f hf Φ hΦ using hφ

  have hspan : Ideal.span (Set.range f) = ⊤ := by
    by_contra h1
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h1
    exact hf ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))

  have h1 : (1 : B) ∈ Ideal.span (Set.range f) := by rw [hspan]; trivial
  obtain ⟨S0, hS0sub, h1S0⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hpre : ∀ s : S0, ∃ x : PrimeSpectrum B, f x = s := fun s => hS0sub s.2
  choose idx hidx using hpre
  let k := S0.card
  let e : Fin k → PrimeSpectrum B := fun i => idx (S0.equivFin.symm i)
  let fe : Fin k → B := fun i => f (e i)
  have he : Ideal.span (Set.range fe) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have hrange : Set.range fe = (S0 : Set B) := by
      ext b
      constructor
      · rintro ⟨i, rfl⟩; show f (idx (S0.equivFin.symm i)) ∈ (S0 : Set B); rw [hidx]; exact (S0.equivFin.symm i).2
      · intro hb; exact ⟨S0.equivFin ⟨b, hb⟩, by simp [fe, e, hidx]⟩
    rw [hrange]; exact h1S0

  let M : Fin k → Type u := fun i => LocalizedModule (Submonoid.powers (fe i)) T
  let M₂ : Fin k → Fin k → Type u := fun i j =>
    LocalizedModule (Submonoid.powers (fe i)) (LocalizedModule (Submonoid.powers (fe j)) T)
  let π : ∀ i, T →ₗ[B] M i := fun i => LocalizedModule.mkLinearMap (Submonoid.powers (fe i)) T
  let ρr : ∀ i j, M j →ₗ[B] M₂ i j := fun i j =>
    LocalizedModule.mkLinearMap (Submonoid.powers (fe i)) (LocalizedModule (Submonoid.powers (fe j)) T)
  let ρl : ∀ i j, M i →ₗ[B] M₂ i j := fun i j =>
    ((LocalizedModule.map (Submonoid.powers (fe i)))
      (LocalizedModule.mkLinearMap (Submonoid.powers (fe j)) T)).restrictScalars B
  have hρl : ∀ i j (t : T) (s : Submonoid.powers (fe i)),
      ρl i j (LocalizedModule.mk t s) = LocalizedModule.mk (LocalizedModule.mk t 1) s := by
    intro i j t s
    show ((LocalizedModule.map (Submonoid.powers (fe i))) (LocalizedModule.mkLinearMap (Submonoid.powers (fe j)) T))
      (LocalizedModule.mk t s) = _
    rw [LocalizedModule.map_mk]; rfl
  have hπc : ∀ i j, ρl i j ∘ₗ π i = ρr i j ∘ₗ π j := by
    intro i j; ext t
    show ρl i j (LocalizedModule.mk t 1) = LocalizedModule.mk (LocalizedModule.mk t 1) 1
    rw [hρl]
  let g : ∀ i, T' →ₗ[B] M i := fun i => Φ (e i)

  have hg : ∀ i j, ρl i j ∘ₗ g i = ρr i j ∘ₗ g j := by
    intro i j; ext a
    obtain ⟨t, n, ht⟩ := exists_rep (fe i) (Φ (e i) a)
    obtain ⟨t', m, ht'⟩ := exists_rep (fe j) (Φ (e j) a)
    show ρl i j (Φ (e i) a) = LocalizedModule.mk (Φ (e j) a) 1
    rw [ht, ht', hρl]
    apply mk_mk_eq_of_forall_prime
    intro y hyi hyj
    have hsi : fe i ^ n ∈ y.asIdeal.primeCompl := fun hh => hyi (y.isPrime.mem_of_pow_mem n hh)
    have hsj : fe j ^ m ∈ y.asIdeal.primeCompl := fun hh => hyj (y.isPrime.mem_of_pow_mem m hh)
    have e1 := hΦ (e i) y hyi a t n ht ⟨fe i ^ n, hsi⟩ rfl
    have e2 := hΦ (e j) y hyj a t' m ht' ⟨fe j ^ m, hsj⟩ rfl
    rw [e1, LocalizedModule.mk_eq] at e2
    obtain ⟨u, hu⟩ := e2
    refine ⟨u, u.2, ?_⟩
    simpa only [Submonoid.smul_def] using hu

  obtain ⟨G, hG, -⟩ := IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top fe he M M₂ ρl ρr
    (fun i j => inferInstance) T π (fun i => inferInstance) hπc T' g hg
  refine ⟨G, fun x a => ?_⟩

  have hex : ∃ i, fe i ∉ x.asIdeal := by
    by_contra hne
    push Not at hne
    have : Ideal.span (Set.range fe) ≤ x.asIdeal := Ideal.span_le.2 (Set.range_subset_iff.2 hne)
    rw [he, top_le_iff] at this
    exact x.isPrime.ne_top this
  obtain ⟨i, hi⟩ := hex
  have hGi : Φ (e i) a = LocalizedModule.mk (G a) (⟨fe i ^ 0, 0, rfl⟩ : Submonoid.powers (fe i)) := by
    have := LinearMap.congr_fun (hG i) a
    rw [LinearMap.comp_apply] at this
    change LocalizedModule.mk (G a) 1 = Φ (e i) a at this
    rw [← this]; congr 1; exact Subtype.ext (pow_zero _).symm
  have := hΦ (e i) x hi a (G a) 0 hGi 1 (by simp)
  exact this.symm

end S_LinearMap_exists_forall_localizedModule_mk_eq_of_forall_exists_chart
end P2MW
export P2MW.S_LinearMap_exists_forall_localizedModule_mk_eq_of_forall_exists_chart (solution)
