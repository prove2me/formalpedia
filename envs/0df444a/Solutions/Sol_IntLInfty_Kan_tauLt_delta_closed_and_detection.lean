-- Prove2me | solution 1 for IntLInfty.Kan.tauLt_delta_closed_and_detection
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T04:02:25.055902+00:00
-- url     : https://prove2.me/submissions/49caa600-ff2e-4498-b68d-8e53e8c88360

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

set_option autoImplicit false

-- slice of scratch/probe/a83e3b53.lean: A83 basics L173-227, A83Tau L4099-4271, A83Det L4275-4658

namespace IntLInfty.Kan.A83

open IntLInfty.Kan

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem lowAlg_mono {p q : ℕ} (h : p ≤ q) : lowAlg L p ≤ lowAlg L q := by
  apply Algebra.adjoin_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨k, hk, hx⟩ := hx
  exact ⟨k, hk.trans h, hx⟩

theorem gen_mem_lowAlg {k p : ℕ} (h : k ≤ p) (ξ : Module.Dual ℝ (L k)) :
    gen L k ξ ∈ lowAlg L p := by
  apply Algebra.subset_adjoin
  simp only [Set.mem_iUnion]
  exact ⟨k, h, ξ, rfl⟩

theorem ceDeg_le_lowAlg (n : ℕ) :
    ceDeg L (n + 1) ≤ Subalgebra.toSubmodule (lowAlg L n) := by
  apply Submodule.span_le.mpr
  rintro x ⟨m, d, ξ, hsum, rfl⟩
  apply Subalgebra.list_prod_mem
  intro y hy
  rw [List.mem_ofFn] at hy
  obtain ⟨t, rfl⟩ := hy
  apply gen_mem_lowAlg
  have : d t + 1 ≤ ∑ s, (d s + 1) :=
    Finset.single_le_sum (f := fun s => d s + 1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  omega

theorem gen_mem_ceDeg (k : ℕ) (ξ : Module.Dual ℝ (L k)) : gen L k ξ ∈ ceDeg L (k + 1) := by
  apply Submodule.subset_span
  refine ⟨1, fun _ => k, fun _ => ξ, by simp, by simp⟩

theorem one_mem_ceDeg : (1 : CE L) ∈ ceDeg L 0 := by
  apply Submodule.subset_span
  refine ⟨0, Fin.elim0, fun t => Fin.elim0 t, by simp, by simp⟩

theorem delta_one (δ : LInfty L) : δ.δ 1 = 0 := by
  have h := δ.leibniz 0 1 one_mem_ceDeg 1
  simp only [mul_one, pow_zero, one_smul, one_mul] at h
  have h2 : δ.δ 1 + δ.δ 1 = δ.δ 1 := h.symm
  simpa using h2

theorem delta_delta (δ : LInfty L) (x : CE L) : δ.δ (δ.δ x) = 0 := by
  have := congrArg (fun f => f x) δ.sq
  simpa using this

theorem delta_gen_mem (δ : LInfty L) (k : ℕ) (ξ : Module.Dual ℝ (L k)) :
    δ.δ (gen L k ξ) ∈ lowAlg L (k + 1) :=
  ceDeg_le_lowAlg (k + 1) (δ.deg _ _ (gen_mem_ceDeg k ξ))

end IntLInfty.Kan.A83

namespace IntLInfty.Kan.A83Tau

open IntLInfty.Kan IntLInfty.Kan.A83

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

/-- Derivation closure: if `δ` maps a set of generators into a subalgebra containing them, it maps
the subalgebra they generate into it. -/
theorem delta_adjoin (δ : LInfty L) (s : Set (CE L))
    (hs : ∀ a ∈ s, ∃ k, ∃ ξ : Module.Dual ℝ (L k), a = gen L k ξ)
    (T : Subalgebra ℝ (CE L)) (hsT : s ⊆ T) (hδ : ∀ a ∈ s, δ.δ a ∈ T) :
    ∀ x ∈ Algebra.adjoin ℝ s, δ.δ x ∈ T := by
  intro x hx
  have hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ s) := hx
  rw [Algebra.adjoin_eq_span] at hx'
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    induction hy using Submonoid.closure_induction_left with
    | one => rw [delta_one]; exact Subalgebra.zero_mem _
    | mul_left a ha b hb ih =>
      have hb' : b ∈ T := by
        have hb2 : b ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ s) := by
          rw [Algebra.adjoin_eq_span]; exact Submodule.subset_span hb
        exact Algebra.adjoin_le hsT hb2
      have hδa := hδ a ha
      have haT := hsT ha
      obtain ⟨k, ξ, rfl⟩ := hs a ha
      rw [δ.leibniz (k + 1) _ (gen_mem_ceDeg k ξ) b]
      exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hδa hb')
        (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ haT ih) _)
  | zero => rw [map_zero]; exact Subalgebra.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Subalgebra.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Subalgebra.smul_mem _ ha r

/-- `A_S` is `δ`-closed as soon as `δ` of every generator of `S` lies in `A_S`. -/
theorem delta_genAlg_of_gen (δ : LInfty L) (S : GenSys L)
    (h : ∀ k (ξ : Module.Dual ℝ (L k)), ξ ∈ S k → δ.δ (gen L k ξ) ∈ genAlg L S)
    (x : CE L) (hx : x ∈ genAlg L S) : δ.δ x ∈ genAlg L S := by
  let s : Set (CE L) :=
    ⋃ i, (gen L i : Module.Dual ℝ (L i) → CE L) '' (S i : Set (Module.Dual ℝ (L i)))
  have hs : ∀ a ∈ s, ∃ k, ∃ ξ : Module.Dual ℝ (L k), a = gen L k ξ := by
    intro a ha
    obtain ⟨i, ξ, _, rfl⟩ := Set.mem_iUnion.1 ha
    exact ⟨i, ξ, rfl⟩
  have hsT : s ⊆ (genAlg L S : Set (CE L)) := fun a ha => Algebra.subset_adjoin ha
  have hδ : ∀ a ∈ s, δ.δ a ∈ genAlg L S := by
    intro a ha
    obtain ⟨i, ξ, hξ, rfl⟩ := Set.mem_iUnion.1 ha
    exact h i ξ hξ
  exact delta_adjoin δ s hs (genAlg L S) hsT hδ x hx

theorem gen_cast {j p : ℕ} (h : j = p) (ζ : Module.Dual ℝ (L j)) :
    ∃ η : Module.Dual ℝ (L p), gen L j ζ = gen L p η := by
  subst h; exact ⟨ζ, rfl⟩

/-- Degree `p + 2` = generators of index `≤ p` plus one linear generator of index `p + 1`. -/
theorem ceDeg_succ_succ_le (p : ℕ) :
    ceDeg L (p + 2) ≤ Subalgebra.toSubmodule (lowAlg L p) ⊔ LinearMap.range (gen L (p + 1)) := by
  apply Submodule.span_le.mpr
  rintro x ⟨k, d, ξ, hsum, rfl⟩
  by_cases hall : ∀ t, d t ≤ p
  · apply Submodule.mem_sup_left
    apply Subalgebra.list_prod_mem
    intro y hy
    rw [List.mem_ofFn] at hy
    obtain ⟨t, rfl⟩ := hy
    exact gen_mem_lowAlg (hall t) _
  · push Not at hall
    obtain ⟨t, ht⟩ := hall
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin k)) (fun s => d s + 1)
      (Finset.mem_univ t)
    have hzero : ∑ s ∈ Finset.univ.erase t, (d s + 1) = 0 := by omega
    have hall1 : ∀ s : Fin k, s = t := by
      intro s
      by_contra hst
      have hmem : s ∈ Finset.univ.erase t := Finset.mem_erase.2 ⟨hst, Finset.mem_univ s⟩
      have := (Finset.sum_eq_zero_iff.1 hzero) s hmem
      omega
    have hk1 : k ≤ 1 := by
      have := Fintype.card_le_one_iff.2 (fun a b : Fin k => (hall1 a).trans (hall1 b).symm)
      simpa using this
    have hk : k = 1 := by
      have : 0 < k := Fin.pos t
      omega
    subst hk
    apply Submodule.mem_sup_right
    have ht0 : t = 0 := Subsingleton.elim _ _
    subst ht0
    have hd : d 0 = p + 1 := by
      simp only [Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero] at hsum
      omega
    obtain ⟨η, hη⟩ := gen_cast hd (ξ 0)
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    rw [hη]
    exact ⟨η, rfl⟩

theorem lowAlg_le_tauLt (δ : LInfty L) {p n : ℕ} (h : p < n) :
    lowAlg L p ≤ genAlg L (tauLt δ n) := by
  apply Algebra.adjoin_le
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨k, hk, ξ, rfl⟩ := hx
  apply gen_mem_genAlg
  show ξ ∈ tauLt δ n k
  simp [tauLt, show k < n by omega]

theorem delta_gen_tauLt_low (δ : LInfty L) (n k : ℕ) (hk : k < n) (ξ : Module.Dual ℝ (L k)) :
    δ.δ (gen L k ξ) ∈ genAlg L (tauLt δ n) := by
  by_cases h : k + 1 < n
  · exact lowAlg_le_tauLt δ h (delta_gen_mem δ k ξ)
  · have hn : n = k + 1 := by omega
    have hx := ceDeg_succ_succ_le (L := L) k (δ.deg _ _ (gen_mem_ceDeg k ξ))
    obtain ⟨y, hy, z, ⟨η, rfl⟩, hyz⟩ := Submodule.mem_sup.1 hx
    rw [← hyz]
    refine Subalgebra.add_mem _ (lowAlg_le_tauLt δ (by omega) hy) (gen_mem_genAlg _ ?_)
    show η ∈ tauLt δ n (k + 1)
    subst hn
    have hη : η ∈ imSub δ (k + 1) := by
      simp only [imSub, Submodule.mem_map, Submodule.mem_comap]
      refine ⟨(ξ, η), ?_, rfl⟩
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, Subalgebra.mem_toSubmodule]
      rw [← hyz]
      simpa using hy
    simpa [tauLt] using hη

theorem delta_gen_tauLt (δ : LInfty L) (n k : ℕ) (ξ : Module.Dual ℝ (L k))
    (hξ : ξ ∈ tauLt δ n k) : δ.δ (gen L k ξ) ∈ genAlg L (tauLt δ n) := by
  by_cases hk : k < n
  · exact delta_gen_tauLt_low δ n k hk ξ
  by_cases hkn : k = n
  · subst hkn
    have hξ' : ξ ∈ imSub δ k := by simpa [tauLt] using hξ
    cases k with
    | zero =>
      have h0 : ξ = 0 := by simpa [imSub] using hξ'
      subst h0
      simp only [map_zero]
      exact Subalgebra.zero_mem _
    | succ p =>
      simp only [imSub, Submodule.mem_map, Submodule.mem_comap] at hξ'
      obtain ⟨⟨η, ξ'⟩, ha, hξeq⟩ := hξ'
      simp only [LinearMap.snd_apply] at hξeq
      subst hξeq
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, Subalgebra.mem_toSubmodule] at ha
      have hg : gen L (p + 1) ξ' =
          δ.δ (gen L p η) - (δ.δ (gen L p η) - gen L (p + 1) ξ') := by abel
      rw [hg, map_sub, delta_delta, zero_sub]
      apply Subalgebra.neg_mem
      refine delta_adjoin δ (⋃ k, ⋃ (_ : k ≤ p), Set.range (gen L k)) ?_ _ ?_ ?_ _ ha
      · intro a ha'
        simp only [Set.mem_iUnion] at ha'
        obtain ⟨k, _, ζ, rfl⟩ := ha'
        exact ⟨k, ζ, rfl⟩
      · intro a ha'
        exact lowAlg_le_tauLt δ (Nat.lt_succ_self p) (Algebra.subset_adjoin ha')
      · intro a ha'
        simp only [Set.mem_iUnion] at ha'
        obtain ⟨k, hk', ζ, rfl⟩ := ha'
        exact delta_gen_tauLt_low δ (p + 1) k (by omega) ζ
  · have h0 : ξ = 0 := by simpa [tauLt, hk, hkn] using hξ
    subst h0
    simp only [map_zero]
    exact Subalgebra.zero_mem _

/-- (3c, first half) `A_{τ<n L}` is a sub-DGA. -/
theorem delta_genAlg_tauLt (δ : LInfty L) (n : ℕ) (x : CE L) (hx : x ∈ genAlg L (tauLt δ n)) :
    δ.δ x ∈ genAlg L (tauLt δ n) :=
  delta_genAlg_of_gen δ _ (fun k ξ hξ => delta_gen_tauLt δ n k ξ hξ) x hx

end IntLInfty.Kan.A83Tau

namespace IntLInfty.Kan.A83Det

open IntLInfty.Kan IntLInfty.Kan.A83
open scoped TensorProduct

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

section Lift

variable {A : Type} [Ring A] [Algebra ℝ A]

noncomputable def gE (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] A) :
    DirectSum {i : ℕ // Even i} (fun i => Module.Dual ℝ (L i.1)) →ₗ[ℝ] A :=
  DirectSum.toModule ℝ {i : ℕ // Even i} A (fun i => f i.1)

def CenterOdd (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] A) : Prop :=
  ∀ i, Odd i → ∀ ξ, f i ξ ∈ Subalgebra.center ℝ A

noncomputable def gSi (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] A) (hS : CenterOdd f)
    (i : {i : ℕ // Odd i}) : Module.Dual ℝ (L i.1) →ₗ[ℝ] Subalgebra.center ℝ A where
  toFun ξ := ⟨f i.1 ξ, hS i.1 i.2 ξ⟩
  map_add' ξ η := Subtype.ext (map_add (f i.1) ξ η)
  map_smul' c ξ := Subtype.ext (map_smul (f i.1) c ξ)

noncomputable def gS (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] A) (hS : CenterOdd f) :
    DirectSum {i : ℕ // Odd i} (fun i => Module.Dual ℝ (L i.1)) →ₗ[ℝ] Subalgebra.center ℝ A :=
  DirectSum.toModule ℝ {i : ℕ // Odd i} _ (gSi f hS)

/-- Algebra map out of `C∗(L)` into any algebra, from generator values (exterior values square to
zero, symmetric values central). -/
noncomputable def liftCE (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] A) (hE : ∀ v, gE f v * gE f v = 0)
    (hS : CenterOdd f) : CE L →ₐ[ℝ] A :=
  Algebra.TensorProduct.lift (ExteriorAlgebra.lift ℝ ⟨gE f, hE⟩)
    ((Subalgebra.center ℝ A).val.comp (SymmetricAlgebra.lift (gS f hS)))
    (fun x y => by
      have hy := ((SymmetricAlgebra.lift (gS f hS)) y).2
      rw [Subalgebra.mem_center_iff] at hy
      exact hy _)

theorem liftCE_gen (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] A) (hE : ∀ v, gE f v * gE f v = 0)
    (hS : CenterOdd f) (i : ℕ) (ξ : Module.Dual ℝ (L i)) :
    liftCE f hE hS (gen L i ξ) = f i ξ := by
  unfold gen
  by_cases h : Even i
  · rw [dif_pos h]
    simp [liftCE, Algebra.TensorProduct.lift_tmul, gE]
  · rw [dif_neg h]
    simp [liftCE, Algebra.TensorProduct.lift_tmul, gS, gSi]

theorem hE_of_range (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] A) {W : Type} [AddCommGroup W]
    [Module ℝ W] (j : W →ₗ[ℝ] A) (hj : ∀ w, j w * j w = 0)
    (hf : ∀ i, Even i → ∀ ξ, f i ξ ∈ LinearMap.range j) :
    ∀ v, gE f v * gE f v = 0 := by
  intro v
  have hv : gE f v ∈ LinearMap.range j := by
    induction v using DirectSum.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | of i x =>
      have : gE f (DirectSum.of _ i x) = f i.1 x := by
        rw [gE, ← DirectSum.lof_eq_of ℝ, DirectSum.toModule_lof]
      rw [this]; exact hf i.1 i.2 x
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  obtain ⟨w, hw⟩ := hv
  rw [← hw]; exact hj w

end Lift

/-- The product map `L∗₀ ⊗ L∗_q → C∗(L)`, `a ⊗ c ↦ gen a * gen c`. -/
noncomputable def Bprod (q : ℕ) :
    Module.Dual ℝ (L 0) ⊗[ℝ] Module.Dual ℝ (L q) →ₗ[ℝ] CE L :=
  TensorProduct.lift (((LinearMap.mul ℝ (CE L)).compl₂ (gen L q)) ∘ₗ gen L 0)

theorem Bprod_tmul (q : ℕ) (a : Module.Dual ℝ (L 0)) (c : Module.Dual ℝ (L q)) :
    Bprod q (a ⊗ₜ c) = gen L 0 a * gen L q c := by
  simp [Bprod]

/-! ### odd top index: target `Polynomial (DualNumber ℝ)` -/

section OddTop

abbrev AP : Type := Polynomial (DualNumber ℝ)

/-- generator values: `L∗₀ ∋ a ↦ α a • ε`, `L∗_q ∋ c ↦ γ c • X`, all other generators `↦ 0`. -/
noncomputable def fP (q : ℕ) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] AP :=
  Function.update (Function.update (0 : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] AP) 0
    (α.smulRight (Polynomial.C DualNumber.eps))) q (γ.smulRight Polynomial.X)

theorem fP_zero {q : ℕ} (hq : q ≠ 0) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) : fP q α γ 0 = α.smulRight (Polynomial.C DualNumber.eps) := by
  rw [fP, Function.update_of_ne (Ne.symm hq), Function.update_self]

theorem fP_top (q : ℕ) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) : fP q α γ q = γ.smulRight Polynomial.X := by
  rw [fP, Function.update_self]

theorem fP_other {q i : ℕ} (h0 : i ≠ 0) (hq : i ≠ q) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) : fP q α γ i = 0 := by
  rw [fP, Function.update_of_ne hq, Function.update_of_ne h0]
  rfl

theorem fP_hE {q : ℕ} (hq : Odd q) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) : ∀ v, gE (fP q α γ) v * gE (fP q α γ) v = 0 := by
  have hq0 : q ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hq)
  refine hE_of_range _ (LinearMap.toSpanSingleton ℝ AP (Polynomial.C DualNumber.eps)) ?_ ?_
  · intro w
    simp only [LinearMap.toSpanSingleton_apply]
    rw [smul_mul_smul, ← Polynomial.C_mul, DualNumber.eps_mul_eps, Polynomial.C_0, smul_zero]
  · intro i hi ξ
    by_cases h0 : i = 0
    · subst h0
      rw [fP_zero hq0]
      exact ⟨α ξ, by simp⟩
    · have hiq : i ≠ q := by rintro rfl; exact (Nat.not_even_iff_odd.2 hq) hi
      rw [fP_other h0 hiq]
      exact ⟨0, by simp⟩

theorem fP_hS (q : ℕ) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) : CenterOdd (fP q α γ) :=
  fun _ _ _ => Subalgebra.mem_center_iff.2 (fun y => by exact mul_comm y _)

noncomputable def thP {q : ℕ} (hq : Odd q) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) : CE L →ₐ[ℝ] AP :=
  liftCE (fP q α γ) (fP_hE hq α γ) (fP_hS q α γ)

/-- constants -/
noncomputable def constP : Subalgebra ℝ AP :=
  (IsScalarTower.toAlgHom ℝ (DualNumber ℝ) AP).range

theorem coeff_one_of_constP {x : AP} (hx : x ∈ constP) : x.coeff 1 = 0 := by
  obtain ⟨d, rfl⟩ := hx
  simp

theorem thP_lowAlg {p : ℕ} (hq : Odd (p + 1)) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L (p + 1)))) :
    lowAlg L p ≤ constP.comap (thP hq α γ) := by
  apply Algebra.adjoin_le
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨k, hk, ξ, rfl⟩ := hx
  show thP hq α γ (gen L k ξ) ∈ constP
  rw [thP, liftCE_gen]
  by_cases h0 : k = 0
  · subst h0
    rw [fP_zero (Nat.succ_ne_zero p)]
    refine ⟨α ξ • DualNumber.eps, ?_⟩
    simp [Polynomial.smul_C]
  · rw [fP_other h0 (by omega)]
    exact Subalgebra.zero_mem _

/-- (DetGen, odd top index) `gen_{p+1}` is injective modulo `lowAlg p`. -/
theorem detGen_odd {p : ℕ} (hq : Odd (p + 1)) (c : Module.Dual ℝ (L (p + 1)))
    (hc : gen L (p + 1) c ∈ lowAlg L p) : c = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℝ c]
  intro γ
  have h : thP hq 0 γ (gen L (p + 1) c) ∈ constP := thP_lowAlg hq 0 γ hc
  have h1 := coeff_one_of_constP h
  rw [thP, liftCE_gen, fP_top] at h1
  have h2 := congrArg TrivSqZeroExt.fst h1
  simpa using h2

noncomputable def lamP : AP →ₗ[ℝ] ℝ where
  toFun x := (x.coeff 1).snd
  map_add' x y := by simp [Polynomial.coeff_add]
  map_smul' c x := by simp [Polynomial.coeff_smul]

/-- (DetProd, odd top index) `Bprod` is injective modulo `lowAlg p`. -/
theorem detProd_odd {p : ℕ} (hq : Odd (p + 1))
    (t : Module.Dual ℝ (L 0) ⊗[ℝ] Module.Dual ℝ (L (p + 1)))
    (ht : Bprod (p + 1) t ∈ lowAlg L p) : t = 0 := by
  let b0 := Module.Basis.ofVectorSpace ℝ (Module.Dual ℝ (L 0))
  let b1 := Module.Basis.ofVectorSpace ℝ (Module.Dual ℝ (L (p + 1)))
  apply (b0.tensorProduct b1).repr.injective
  ext ⟨i, j⟩
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have key : ∀ s, lamP (thP hq (b0.coord i) (b1.coord j) (Bprod (p + 1) s)) =
      (b0.tensorProduct b1).repr s (i, j) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    | tmul a c =>
      rw [Bprod_tmul, map_mul, thP, liftCE_gen, liftCE_gen, fP_zero (Nat.succ_ne_zero p), fP_top,
        Module.Basis.tensorProduct_repr_tmul_apply]
      simp only [LinearMap.smulRight_apply, Module.Basis.coord_apply, lamP, LinearMap.coe_mk,
        AddHom.coe_mk]
      rw [smul_mul_smul, Polynomial.coeff_smul, Polynomial.coeff_C_mul_X]
      simp only [↓reduceIte, TrivSqZeroExt.snd_smul, DualNumber.snd_eps, smul_eq_mul, mul_comm, one_mul]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, Finsupp.add_apply]
  rw [← key]
  have h : thP hq (b0.coord i) (b1.coord j) (Bprod (p + 1) t) ∈ constP :=
    thP_lowAlg hq (b0.coord i) (b1.coord j) ht
  have h1 := coeff_one_of_constP h
  simp only [lamP, LinearMap.coe_mk, AddHom.coe_mk, h1, TrivSqZeroExt.snd_zero]

end OddTop

/-! ### even top index: target `ExteriorAlgebra ℝ (Fin 2 → ℝ)` -/

section EvenTop

abbrev WX : Type := Fin 2 → ℝ
abbrev AX : Type := ExteriorAlgebra ℝ WX

noncomputable def eX (k : Fin 2) : WX := Pi.single k 1
noncomputable def dX (k : Fin 2) : Module.Dual ℝ WX := LinearMap.proj k

theorem dX_eX (k l : Fin 2) : dX k (eX l) = if k = l then 1 else 0 := by
  by_cases h : k = l
  · subst h; simp [dX, eX]
  · simp [dX, eX, h]

noncomputable def fX (q : ℕ) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] AX :=
  Function.update (Function.update (0 : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] AX) 0
    ((ExteriorAlgebra.ι ℝ) ∘ₗ α.smulRight (eX 0))) q ((ExteriorAlgebra.ι ℝ) ∘ₗ γ.smulRight (eX 1))

theorem fX_zero {q : ℕ} (hq : q ≠ 0) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) :
    fX q α γ 0 = (ExteriorAlgebra.ι ℝ) ∘ₗ α.smulRight (eX 0) := by
  rw [fX, Function.update_of_ne (Ne.symm hq), Function.update_self]

theorem fX_top (q : ℕ) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) :
    fX q α γ q = (ExteriorAlgebra.ι ℝ) ∘ₗ γ.smulRight (eX 1) := by
  rw [fX, Function.update_self]

theorem fX_other {q i : ℕ} (h0 : i ≠ 0) (hq : i ≠ q) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) : fX q α γ i = 0 := by
  rw [fX, Function.update_of_ne hq, Function.update_of_ne h0]
  rfl

theorem fX_hE {q : ℕ} (hq0 : q ≠ 0) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) : ∀ v, gE (fX q α γ) v * gE (fX q α γ) v = 0 := by
  refine hE_of_range _ (ExteriorAlgebra.ι ℝ) (fun w => ExteriorAlgebra.ι_sq_zero w) ?_
  intro i _ ξ
  by_cases h0 : i = 0
  · subst h0
    rw [fX_zero hq0]
    exact ⟨α ξ • eX 0, rfl⟩
  · by_cases hiq : i = q
    · subst hiq
      rw [fX_top]
      exact ⟨γ ξ • eX 1, rfl⟩
    · rw [fX_other h0 hiq]
      exact ⟨0, by simp⟩

theorem fX_hS {q : ℕ} (hq : Even q) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) : CenterOdd (fX q α γ) := by
  intro i hi ξ
  have h0 : i ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hi
  have hiq : i ≠ q := by rintro rfl; exact (Nat.not_even_iff_odd.2 hi) hq
  rw [fX_other h0 hiq]
  exact Subalgebra.zero_mem _

noncomputable def thX {q : ℕ} (hq : Even q) (hq0 : q ≠ 0) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L q))) : CE L →ₐ[ℝ] AX :=
  liftCE (fX q α γ) (fX_hE hq0 α γ) (fX_hS hq α γ)

/-- the subalgebra spanned by `1` and `e₀` -/
noncomputable def lowX : Subalgebra ℝ AX := Algebra.adjoin ℝ {ExteriorAlgebra.ι ℝ (eX 0)}

theorem lowX_form {x : AX} (hx : x ∈ lowX) :
    ∃ a b : ℝ, x = a • (1 : AX) + b • ExteriorAlgebra.ι ℝ (eX 0) := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, 1, by rw [hy]; simp⟩
  | algebraMap r => exact ⟨r, 0, by rw [Algebra.algebraMap_eq_smul_one]; simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, d, rfl⟩ := hz
    exact ⟨a + c, b + d, by module⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, d, rfl⟩ := hz
    refine ⟨a * c, a * d + b * c, ?_⟩
    simp only [add_mul, mul_add, smul_mul_smul, one_mul, mul_one, ExteriorAlgebra.ι_sq_zero,
      smul_zero, add_zero]
    module

theorem thX_lowAlg {p : ℕ} (hq : Even (p + 1)) (α : Module.Dual ℝ (Module.Dual ℝ (L 0)))
    (γ : Module.Dual ℝ (Module.Dual ℝ (L (p + 1)))) :
    lowAlg L p ≤ lowX.comap (thX hq (Nat.succ_ne_zero p) α γ) := by
  apply Algebra.adjoin_le
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨k, hk, ξ, rfl⟩ := hx
  show thX hq (Nat.succ_ne_zero p) α γ (gen L k ξ) ∈ lowX
  rw [thX, liftCE_gen]
  by_cases h0 : k = 0
  · subst h0
    rw [fX_zero (Nat.succ_ne_zero p)]
    have hξ : ((ExteriorAlgebra.ι ℝ) ∘ₗ α.smulRight (eX 0)) ξ =
        α ξ • ExteriorAlgebra.ι ℝ (eX 0) := by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smulRight_apply, map_smul]
    rw [hξ]
    exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _
  · rw [fX_other h0 (by omega)]
    exact Subalgebra.zero_mem _

noncomputable def lamX1 : AX →ₗ[ℝ] ℝ :=
  (ExteriorAlgebra.algebraMapInv : AX →ₐ[ℝ] ℝ).toLinearMap ∘ₗ
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ WX)) (dX 1)

noncomputable def lamX2 : AX →ₗ[ℝ] ℝ :=
  lamX1 ∘ₗ CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ WX)) (dX 0)

theorem lamX_lowX {x : AX} (hx : x ∈ lowX) : lamX1 x = 0 ∧ lamX2 x = 0 := by
  obtain ⟨a, b, rfl⟩ := lowX_form hx
  have h1 : (1 : AX) = algebraMap ℝ AX 1 := (map_one _).symm
  simp only [lamX1, lamX2, LinearMap.coe_comp, Function.comp_apply, map_add, map_smul, h1,
    CliffordAlgebra.contractLeft_algebraMap, CliffordAlgebra.contractLeft_ι, dX_eX]
  simp

theorem cl_ι_mul (d : Module.Dual ℝ WX) (a : WX) (b : AX) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ WX)) d (ExteriorAlgebra.ι ℝ a * b) =
      d a • b - ExteriorAlgebra.ι ℝ a *
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ WX)) d b :=
  CliffordAlgebra.contractLeft_ι_mul _ _ _

theorem cl_ι (d : Module.Dual ℝ WX) (a : WX) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ WX)) d (ExteriorAlgebra.ι ℝ a) =
      algebraMap ℝ AX (d a) :=
  CliffordAlgebra.contractLeft_ι _ _ _

theorem lamX2_e01 :
    lamX2 (ExteriorAlgebra.ι ℝ (eX 0) * ExteriorAlgebra.ι ℝ (eX 1)) = 1 := by
  simp only [lamX2, lamX1, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  rw [cl_ι_mul, cl_ι, dX_eX, dX_eX]
  simp [cl_ι, dX_eX]

/-- (DetGen, even top index) -/
theorem detGen_even {p : ℕ} (hq : Even (p + 1)) (c : Module.Dual ℝ (L (p + 1)))
    (hc : gen L (p + 1) c ∈ lowAlg L p) : c = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℝ c]
  intro γ
  have h : thX hq (Nat.succ_ne_zero p) 0 γ (gen L (p + 1) c) ∈ lowX := thX_lowAlg hq 0 γ hc
  have h1 := (lamX_lowX h).1
  rw [thX, liftCE_gen, fX_top] at h1
  simpa [lamX1, CliffordAlgebra.contractLeft_ι, dX_eX] using h1

/-- (DetProd, even top index) -/
theorem detProd_even {p : ℕ} (hq : Even (p + 1))
    (t : Module.Dual ℝ (L 0) ⊗[ℝ] Module.Dual ℝ (L (p + 1)))
    (ht : Bprod (p + 1) t ∈ lowAlg L p) : t = 0 := by
  let b0 := Module.Basis.ofVectorSpace ℝ (Module.Dual ℝ (L 0))
  let b1 := Module.Basis.ofVectorSpace ℝ (Module.Dual ℝ (L (p + 1)))
  apply (b0.tensorProduct b1).repr.injective
  ext ⟨i, j⟩
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have key : ∀ s, lamX2 (thX hq (Nat.succ_ne_zero p) (b0.coord i) (b1.coord j) (Bprod (p + 1) s)) =
      (b0.tensorProduct b1).repr s (i, j) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      rw [Bprod_tmul, map_mul, thX, liftCE_gen, liftCE_gen, fX_zero (Nat.succ_ne_zero p), fX_top,
        Module.Basis.tensorProduct_repr_tmul_apply]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smulRight_apply,
        Module.Basis.coord_apply, map_smul, smul_mul_smul, lamX2_e01, smul_eq_mul, mul_one]
      ring
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, Finsupp.add_apply]
  rw [← key]
  have h : thX hq (Nat.succ_ne_zero p) (b0.coord i) (b1.coord j) (Bprod (p + 1) t) ∈ lowX :=
    thX_lowAlg hq (b0.coord i) (b1.coord j) ht
  exact (lamX_lowX h).2

end EvenTop

/-- (DetGen) `gen_{p+1}` is injective modulo `lowAlg p`. -/
theorem detGen {p : ℕ} (c : Module.Dual ℝ (L (p + 1))) (hc : gen L (p + 1) c ∈ lowAlg L p) :
    c = 0 := by
  rcases Nat.even_or_odd (p + 1) with h | h
  · exact detGen_even h c hc
  · exact detGen_odd h c hc

/-- (DetProd) `Bprod` is injective modulo `lowAlg p`. -/
theorem detProd {p : ℕ} (t : Module.Dual ℝ (L 0) ⊗[ℝ] Module.Dual ℝ (L (p + 1)))
    (ht : Bprod (p + 1) t ∈ lowAlg L p) : t = 0 := by
  rcases Nat.even_or_odd (p + 1) with h | h
  · exact detProd_even h t ht
  · exact detProd_odd h t ht

end IntLInfty.Kan.A83Det

open scoped TensorProduct in
open IntLInfty.Kan in
theorem solution {L : ℕ → Type} [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] :
    (∀ (δ : LInfty L) (n : ℕ), ∀ x ∈ genAlg L (tauLt δ n), δ.δ x ∈ genAlg L (tauLt δ n)) ∧
    (∀ (δ : LInfty L) (S : GenSys L),
      (∀ (k : ℕ) (ξ : Module.Dual ℝ (L k)), ξ ∈ S k → δ.δ (gen L k ξ) ∈ genAlg L S) →
      ∀ x ∈ genAlg L S, δ.δ x ∈ genAlg L S) ∧
    (∀ p : ℕ, ceDeg L (p + 2) ≤
      Subalgebra.toSubmodule (lowAlg L p) ⊔ LinearMap.range (gen L (p + 1))) ∧
    (∀ (p : ℕ) (c : Module.Dual ℝ (L (p + 1))), gen L (p + 1) c ∈ lowAlg L p → c = 0) ∧
    (∀ (p : ℕ) (t : Module.Dual ℝ (L 0) ⊗[ℝ] Module.Dual ℝ (L (p + 1))),
      TensorProduct.lift (((LinearMap.mul ℝ (CE L)).compl₂ (gen L (p + 1))) ∘ₗ gen L 0) t ∈
        lowAlg L p → t = 0) := by
  exact
      ⟨fun δ n x hx => IntLInfty.Kan.A83Tau.delta_genAlg_tauLt δ n x hx,
       fun δ S h x hx => IntLInfty.Kan.A83Tau.delta_genAlg_of_gen δ S h x hx,
       fun p => IntLInfty.Kan.A83Tau.ceDeg_succ_succ_le p,
       fun p c hc => IntLInfty.Kan.A83Det.detGen c hc,
       fun p t ht => IntLInfty.Kan.A83Det.detProd t ht⟩
