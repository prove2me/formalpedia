-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_adicCompletion_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:56:05.334943+00:00
-- url     : https://prove2.me/submissions/544109da-858a-44b9-b518-102ec15e6e47

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_exists_small_good_subgroups
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion

open NumberField IsDedekindDomain

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Sol_MasulloGRH_schwartzBruhat_adicCompletion_range_eq

open MasulloGRH Topology Filter Pointwise

section group

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem preconnected_subset_one {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (hG : ∀ U ∈ 𝓝 (1 : G), ∃ H : Subgroup G, IsOpen (H : Set G) ∧ (H : Set G) ⊆ U)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hc : Continuous π) (ho : IsOpenMap π)
    (S : Set (Multiplicative (ElemGroup m n r s d))) (hS : IsPreconnected S)
    (h1 : (1 : Multiplicative (ElemGroup m n r s d)) ∈ S) :
    S ⊆ {1} := by
  have : T1Space (Multiplicative (ElemGroup m n r s d)) :=
    inferInstanceAs (T1Space (ElemGroup m n r s d))
  intro p hp
  by_contra hp1
  have hW : IsOpen (π ⁻¹' {p}ᶜ) := (isOpen_compl_singleton).preimage hc
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hW
  have h1O : (1 : G) ∈ O := by
    have : (1 : Γ) ∈ π ⁻¹' {p}ᶜ := by
      simp only [Set.mem_preimage, map_one, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun h => hp1 h.symm
    rw [← hOeq] at this
    simpa using this
  obtain ⟨H, hHo, hHO⟩ := hG O (hO.mem_nhds h1O)
  let H' : Subgroup Γ := H.subgroupOf Γ
  have hH'o : IsOpen (H' : Set Γ) := hHo.preimage continuous_subtype_val
  let M : Subgroup (Multiplicative (ElemGroup m n r s d)) := H'.map π
  have hMo : IsOpen (M : Set (Multiplicative (ElemGroup m n r s d))) := by
    simpa [M, Subgroup.coe_map] using ho _ hH'o
  have hMc : IsClosed (M : Set (Multiplicative (ElemGroup m n r s d))) :=
    Subgroup.isClosed_of_isOpen M hMo
  have hSM : S ⊆ M := hS.subset_isClopen ⟨hMc, hMo⟩ ⟨1, h1, M.one_mem⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (hSM hp)
  have : y ∈ π ⁻¹' {π y}ᶜ := by
    rw [← hOeq]; exact hHO hy
  exact this rfl

theorem m_eq_zero {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (hG : ∀ U ∈ 𝓝 (1 : G), ∃ H : Subgroup G, IsOpen (H : Set G) ∧ (H : Set G) ⊆ U)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hc : Continuous π) (ho : IsOpenMap π) :
    m = 0 := by
  by_contra hm
  have i : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  let f : ℝ → Multiplicative (ElemGroup m n r s d) :=
    fun t => Multiplicative.ofAdd ((Pi.single i t : Fin m → ℝ), 0, 0, 0)
  have hf : Continuous f := by
    refine continuous_ofAdd.comp ?_
    have hs : Continuous (fun t : ℝ => (Pi.single i t : Fin m → ℝ)) :=
      continuous_single (A := fun _ : Fin m => ℝ) i
    exact hs.prodMk continuous_const
  have hsub := preconnected_subset_one Γ hG π hc ho (Set.range f) (isPreconnected_range hf)
    ⟨0, by simp [f]⟩
  have h1 : f 1 = 1 := hsub ⟨1, rfl⟩
  have := congrArg (fun q => (Multiplicative.toAdd q).1 i) h1
  simp [f] at this

theorem n_eq_zero {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (hG : ∀ U ∈ 𝓝 (1 : G), ∃ H : Subgroup G, IsOpen (H : Set G) ∧ (H : Set G) ⊆ U)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hc : Continuous π) (ho : IsOpenMap π) :
    n = 0 := by
  by_contra hn
  have i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let f : ℝ → Multiplicative (ElemGroup m n r s d) :=
    fun t => Multiplicative.ofAdd (0, (Pi.single i (t : UnitAddCircle) : Fin n → UnitAddCircle),
      0, 0)
  have hf : Continuous f := by
    refine continuous_ofAdd.comp ?_
    have h0 : Continuous (fun t : ℝ => (t : UnitAddCircle)) := AddCircle.continuous_mk' 1
    have hs : Continuous (fun t : UnitAddCircle => (Pi.single i t : Fin n → UnitAddCircle)) :=
      continuous_single (A := fun _ : Fin n => UnitAddCircle) i
    exact continuous_const.prodMk ((hs.comp h0).prodMk continuous_const)
  have hsub := preconnected_subset_one Γ hG π hc ho (Set.range f) (isPreconnected_range hf)
    ⟨0, by simp [f]⟩
  have h1 : f (1 / 2) = 1 := hsub ⟨1 / 2, rfl⟩
  have := congrArg (fun q => (Multiplicative.toAdd q).2.1 i) h1
  simp only [f, toAdd_ofAdd, Pi.single_eq_same, toAdd_one, Prod.snd_zero, Prod.fst_zero,
    Pi.zero_apply] at this
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff 1).mp this
  have hk' : (k : ℝ) = 1 / 2 := by simpa using hk
  have h2 : ((2 * k : ℤ) : ℝ) = 1 := by push_cast; linarith
  have h3 : (2 * k : ℤ) = 1 := by exact_mod_cast h2
  omega

theorem r_eq_zero {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G) (N : ℕ) (hN : N ≠ 0)
    (htors : ∀ x : G, Tendsto (fun j : ℕ => x ^ (N ^ j)) atTop (𝓝 1))
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hc : Continuous π)
    (hsurj : Function.Surjective π) : r = 0 := by
  by_contra hr
  have i : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
  obtain ⟨y, hy⟩ := hsurj (Multiplicative.ofAdd ((0 : Fin m → ℝ), (0 : Fin n → UnitAddCircle),
    (Pi.single i (1 : ℤ) : Fin r → ℤ), (0 : (j : Fin s) → ZMod (d j))))
  let c : Γ → ℤ := fun z => (Multiplicative.toAdd (π z)).2.2.1 i
  have hcc : Continuous c := by
    have : Continuous (fun q : Multiplicative (ElemGroup m n r s d) =>
        (Multiplicative.toAdd q).2.2.1 i) := by
      have h0 : Continuous (Multiplicative.toAdd : Multiplicative (ElemGroup m n r s d) → _) :=
        continuous_toAdd
      fun_prop
    exact this.comp hc
  have ht : Tendsto (fun j : ℕ => y ^ (N ^ j)) atTop (𝓝 1) := by
    rw [tendsto_subtype_rng]; simpa using htors (y : G)
  have h2 : Tendsto (fun j : ℕ => c (y ^ (N ^ j))) atTop (𝓝 (c 1)) := (hcc.tendsto 1).comp ht
  have hc1 : c 1 = 0 := by simp [c]
  rw [hc1, nhds_discrete, tendsto_pure] at h2
  obtain ⟨j, hj⟩ := h2.exists
  have : c (y ^ (N ^ j)) = ((N ^ j : ℕ) : ℤ) := by
    simp [c, map_pow, hy, toAdd_pow]
  rw [this] at hj
  exact pow_ne_zero j hN (by exact_mod_cast hj)

theorem isLocallyConstant_of_invariant (k : Subgroup G) (hk : IsOpen (k : Set G)) (f : G → ℂ)
    (hf : ∀ x, ∀ y ∈ k, f (x * y) = f x) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hcont : Tendsto (fun z => x⁻¹ * z) (𝓝 x) (𝓝 1) := by
    have := (continuous_const_mul x⁻¹).tendsto x
    simpa using this
  filter_upwards [hcont (hk.mem_nhds k.one_mem)] with z hz
  have := hf x _ hz
  simpa using this

theorem exists_nhds_invariant [T2Space G] (h : G → ℂ) (hlc : IsLocallyConstant h)
    (hcs : HasCompactSupport h) :
    ∃ W ∈ 𝓝 (1 : G), ∀ x, ∀ w ∈ W, h (x * w) = h x := by
  let E : Set (G × G) := {p | h (p.1 * p.2) = h p.1}
  have hE : IsOpen E := by
    have h1 : IsLocallyConstant (fun p : G × G => h (p.1 * p.2)) :=
      hlc.comp_continuous continuous_mul
    have h2 : IsLocallyConstant (fun p : G × G => h p.1) := hlc.comp_continuous continuous_fst
    have h3 : IsLocallyConstant (fun p : G × G => (h (p.1 * p.2), h p.1)) := h1.comp₂ h2 Prod.mk
    exact h3 {q | q.1 = q.2}
  have hsub : tsupport h ×ˢ ({1} : Set G) ⊆ E := by
    rintro ⟨x, y⟩ ⟨_, hy⟩
    simp only [Set.mem_singleton_iff] at hy
    simp [E, hy]
  obtain ⟨U, V, -, hV, hKU, h1V, hUV⟩ :=
    generalized_tube_lemma hcs.isCompact isCompact_singleton hE hsub
  have hV1 : V ∈ 𝓝 (1 : G) := hV.mem_nhds (h1V rfl)
  refine ⟨V ∩ V⁻¹, Filter.inter_mem hV1 (inv_mem_nhds_one G hV1), ?_⟩
  intro x w hw
  by_cases hx : x ∈ tsupport h
  · exact hUV (Set.mk_mem_prod (hKU hx) hw.1)
  · by_cases hxw : x * w ∈ tsupport h
    · have : h (x * w * w⁻¹) = h (x * w) := hUV (Set.mk_mem_prod (hKU hxw) hw.2)
      rw [mul_inv_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxw]

theorem extendPullback_mul {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G) (hkΓ : k ≤ Γ)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hker : ∀ x : Γ, π x = 1 ↔ (x : G) ∈ k)
    (g : ElemGroup m n r s d → ℂ) (x y : G) (hy : y ∈ k) :
    extendPullback Γ π g (x * y) = extendPullback Γ π g x := by
  have hyΓ : y ∈ Γ := hkΓ hy
  unfold extendPullback
  by_cases hx : x ∈ Γ
  · have hxy : x * y ∈ Γ := Γ.mul_mem hx hyΓ
    rw [dif_pos hxy, dif_pos hx]
    have : π ⟨x * y, hxy⟩ = π ⟨x, hx⟩ := by
      have e : (⟨x * y, hxy⟩ : Γ) = ⟨x, hx⟩ * ⟨y, hyΓ⟩ := rfl
      rw [e, map_mul, (hker ⟨y, hyΓ⟩).mpr hy, mul_one]
    rw [this]
  · have hxy : x * y ∉ Γ := fun h => hx (by simpa using Γ.mul_mem h (Γ.inv_mem hyΓ))
    rw [dif_neg hxy, dif_neg hx]

theorem isCompact_of_presentation [T2Space G] [LocallyCompactSpace G] {s : ℕ} {d : Fin s → ℕ}
    (Γ k : Subgroup G) (hs : IsStructuralPair Γ k)
    (π : Γ →* Multiplicative (ElemGroup 0 0 0 s d)) (hπ : IsElemPresentation Γ k π) :
    IsCompact (Γ : Set G) := by
  have hk : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hs.2.2.1
  have : ∀ i, NeZero (d i) := fun i => ⟨hπ.1 i⟩
  have : Finite (Multiplicative (ElemGroup 0 0 0 s d)) := inferInstance
  choose σ hσ using hπ.2.2.2.1
  have hR : (Set.range (fun t => (σ t : G))).Finite := Set.finite_range _
  have hRk : IsCompact (Set.range (fun t => (σ t : G)) * (k : Set G)) := hR.isCompact.mul hk
  have hΓc : IsClosed (Γ : Set G) := Subgroup.isClosed_of_isOpen Γ hs.1
  refine hRk.of_isClosed_subset hΓc ?_
  intro x hx
  have hmem := (hπ.2.2.2.2 ((σ (π ⟨x, hx⟩))⁻¹ * ⟨x, hx⟩)).mp
    (by rw [map_mul, map_inv, hσ, inv_mul_cancel])
  refine ⟨σ (π ⟨x, hx⟩), ⟨_, rfl⟩, (σ (π ⟨x, hx⟩) : G)⁻¹ * x, ?_, by simp⟩
  simpa using hmem

end group

theorem isRapidDecay_of_bounded {s : ℕ} {d : Fin s → ℕ} (g : ElemGroup 0 0 0 s d → ℂ) (B : ℝ)
    (hB : ∀ t, ‖g t‖ ≤ B) : IsRapidDecay g := by
  have hconst : ∀ a b, elemLift g a b = fun _ => elemLift g a b 0 :=
    fun a b => funext fun xt => congrArg _ (Subsingleton.elim _ _)
  refine ⟨fun a b => ?_, fun i j k => ⟨B, fun a b xt => ?_⟩⟩
  · rw [hconst a b]; exact contDiff_const
  · have ha : ‖a‖ = 0 := by rw [Subsingleton.elim a 0, norm_zero]
    have hx : ‖xt.1‖ = 0 := by rw [Subsingleton.elim xt.1 0, norm_zero]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    have hpow : ∀ (t : ℝ) (e : ℕ), t = 0 → t ^ e ≤ 1 := by
      intro t e ht; subst ht; rcases e with _ | e <;> simp
    have hD : ‖iteratedFDeriv ℝ k (elemLift g a b) xt‖ ≤ B := by
      rw [hconst a b]
      rcases k with _ | k
      · rw [norm_iteratedFDeriv_zero]; exact hB _
      · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]; simpa using hB0
    have h1 : ‖a‖ ^ j * ‖xt.1‖ ^ i ≤ 1 :=
      mul_le_one₀ (hpow _ _ ha) (by positivity) (hpow _ _ hx)
    calc ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift g a b) xt‖ ≤ 1 * B :=
          mul_le_mul h1 hD (norm_nonneg _) zero_le_one
      _ = B := one_mul B

section adic

variable (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem countable_numberField : Countable F := by
  have h : ({x : F | IsAlgebraic ℚ x}).Countable := Algebraic.countable ℚ F
  have huniv : {x : F | IsAlgebraic ℚ x} = Set.univ :=
    Set.eq_univ_of_forall fun x => Algebra.IsAlgebraic.isAlgebraic x
  rw [huniv] at h
  exact Set.countable_univ_iff.mp h

theorem secondCountable_finite : SecondCountableTopology (v.adicCompletion F) := by
  have : Countable F := countable_numberField F
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨⟨Set.range (algebraMap F (v.adicCompletion F)), Set.countable_range _,
      v.denseRange_algebraMap F⟩⟩
  exact UniformSpace.secondCountable_of_separable _

theorem hG_adic : ∀ U ∈ 𝓝 (1 : Multiplicative (v.adicCompletion F)),
    ∃ H : Subgroup (Multiplicative (v.adicCompletion F)),
      IsOpen (H : Set (Multiplicative (v.adicCompletion F))) ∧
        (H : Set (Multiplicative (v.adicCompletion F))) ⊆ U := by
  intro U hU
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean
    (Multiplicative.ofAdd ⁻¹' U : Set (v.adicCompletion F)) hU
  exact ⟨AddSubgroup.toSubgroup V.toAddSubgroup, V.isOpen, hV⟩

theorem htors_adic : ∀ x : Multiplicative (v.adicCompletion F),
    Tendsto (fun j : ℕ => x ^ (Ideal.absNorm v.asIdeal ^ j)) atTop (𝓝 1) := by
  intro x
  have hN : ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ < 1 := by
    have h := (FinitePlace.norm_lt_one_iff_mem F v ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).mpr
      (Ideal.absNorm_mem _)
    simpa using h
  have h0 : Tendsto (fun j : ℕ => ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) ^ j *
      Multiplicative.toAdd x) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hN).mul_const (Multiplicative.toAdd x)
  have : (fun j : ℕ => x ^ (Ideal.absNorm v.asIdeal ^ j)) = fun j => Multiplicative.ofAdd
      (((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) ^ j * Multiplicative.toAdd x) := by
    funext j
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow, nsmul_eq_mul]
  rw [this]
  have h1 := (continuous_ofAdd.tendsto 0).comp h0
  rw [ofAdd_zero] at h1
  exact h1

end adic

end Sol_MasulloGRH_schwartzBruhat_adicCompletion_range_eq

open Sol_MasulloGRH_schwartzBruhat_adicCompletion_range_eq Topology Filter

open MasulloGRH

theorem solution
    (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Set.range (fun (f : SchwartzBruhat (Multiplicative (v.adicCompletion F)))
        (x : v.adicCompletion F) => f (Multiplicative.ofAdd x)) =
      {h : v.adicCompletion F → ℂ | IsLocallyConstant h ∧ HasCompactSupport h} := by
  classical
  haveI hlcK : LocallyCompactSpace (v.adicCompletion F) :=
    RiemannMasullo.locallyCompactSpace_adicCompletion (K := F) v
  haveI : LocallyCompactSpace (Multiplicative (v.adicCompletion F)) := hlcK
  haveI : SecondCountableTopology (Multiplicative (v.adicCompletion F)) :=
    secondCountable_finite F v
  have hG := hG_adic F v
  have htors := htors_adic F v
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := by
    have := HeightOneSpectrum.one_lt_absNorm v
    omega
  have key : ∀ {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup (Multiplicative (v.adicCompletion F)))
      (π : Γ →* Multiplicative (ElemGroup m n r s d)), IsElemPresentation Γ k π →
      m = 0 ∧ n = 0 ∧ r = 0 := by
    intro m n r s d Γ k π hπ
    exact ⟨m_eq_zero Γ hG π hπ.2.1 hπ.2.2.1, n_eq_zero Γ hG π hπ.2.1 hπ.2.2.1,
      r_eq_zero Γ _ hN htors π hπ.2.1 hπ.2.2.2.1⟩
  ext h
  constructor
  · rintro ⟨f, rfl⟩
    have hall : ∀ φ ∈ schwartzBruhatSubmodule (Multiplicative (v.adicCompletion F)),
        IsLocallyConstant φ ∧ HasCompactSupport φ := by
      intro φ hφ
      induction hφ using Submodule.span_induction with
      | mem φ hφ =>
        obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hφ
        obtain ⟨rfl, rfl, rfl⟩ := key Γ k π hπ
        haveI : DiscreteTopology (Multiplicative (ElemGroup 0 0 0 s d)) :=
          inferInstanceAs (DiscreteTopology (ElemGroup 0 0 0 s d))
        have hkopen : IsOpen (k : Set (Multiplicative (v.adicCompletion F))) := by
          have h1 : IsOpen (π ⁻¹' {1}) := (isOpen_discrete _).preimage hπ.2.1
          have h2 := hs.1.isOpenMap_subtype_val _ h1
          convert h2 using 1
          ext x
          constructor
          · intro hx
            exact ⟨⟨x, hs.2.2.2 hx⟩, (hπ.2.2.2.2 ⟨x, hs.2.2.2 hx⟩).mpr hx, rfl⟩
          · rintro ⟨y, hy, rfl⟩
            exact (hπ.2.2.2.2 y).mp hy
        refine ⟨isLocallyConstant_of_invariant k hkopen _ ?_, ?_⟩
        · intro x y hy
          exact extendPullback_mul Γ k hs.2.2.2 π hπ.2.2.2.2 _ x y hy
        · refine HasCompactSupport.intro (isCompact_of_presentation Γ k hs π hπ) ?_
          intro x hx
          unfold extendPullback
          exact dif_neg (show x ∉ Γ from hx)
      | zero => exact ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
      | add φ ψ _ _ hφ hψ => exact ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩
      | smul c φ _ hφ =>
        refine ⟨hφ.1.comp (fun z => c • z), ?_⟩
        exact hφ.2.mono (Function.support_const_smul_subset c φ)
    exact hall f.1 f.2
  · rintro ⟨hlc, hcs⟩
    let h' : Multiplicative (v.adicCompletion F) → ℂ := fun x => h (Multiplicative.toAdd x)
    have hlc' : IsLocallyConstant h' := hlc
    have hcs' : HasCompactSupport h' := hcs
    obtain ⟨W, hW, hWinv⟩ := exists_nhds_invariant h' hlc' hcs'
    obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : Multiplicative (v.adicCompletion F))
    let U : Set (Multiplicative (v.adicCompletion F)) := C ∪ tsupport h'
    let Γ : Subgroup (Multiplicative (v.adicCompletion F)) := Subgroup.closure U
    have hUΓ : U ⊆ Γ := Subgroup.subset_closure
    have hΓo : IsOpen (Γ : Set (Multiplicative (v.adicCompletion F))) :=
      Subgroup.isOpen_of_mem_nhds Γ (Filter.mem_of_superset hC1 (fun x hx => hUΓ (Or.inl hx)))
    have hΓcg : IsCompactlyGeneratedSubgroup Γ :=
      ⟨U, hCc.union hcs'.isCompact, hUΓ, ⟨C, hC1, fun x hx => Or.inl hx.1⟩, rfl⟩
    obtain ⟨kk, -, hsmall, hgood, hpres⟩ :=
      exists_small_good_subgroups (Multiplicative (v.adicCompletion F))
    obtain ⟨N, hNsub⟩ := hsmall (W ∩ C) (Filter.inter_mem hW hC1)
    have hkΓ : kk N ≤ Γ := fun x hx => hUΓ (Or.inl (hNsub hx).2)
    obtain ⟨m, n, r, s, d, π, hπ⟩ := hpres N Γ hΓo hΓcg hkΓ
    have hs : IsStructuralPair Γ (kk N) := ⟨hΓo, hΓcg, hgood N, hkΓ⟩
    obtain ⟨rfl, rfl, rfl⟩ := key Γ (kk N) π hπ
    choose σ hσ using hπ.2.2.2.1
    let g : ElemGroup 0 0 0 s d → ℂ := fun t => h' (σ (Multiplicative.ofAdd t))
    obtain ⟨B, hB⟩ := hlc'.continuous.bounded_above_of_compact_support hcs'
    have hg : IsRapidDecay g := isRapidDecay_of_bounded g B (fun t => hB _)
    let gS : ElemSchwartz 0 0 0 s d := ⟨g, Submodule.subset_span hg⟩
    refine ⟨SchwartzBruhat.ofElem Γ (kk N) π hs hπ gS, ?_⟩
    funext x
    show extendPullback Γ π g (Multiplicative.ofAdd x) = h x
    unfold extendPullback
    split_ifs with hx
    · simp only [g, ofAdd_toAdd]
      have hy : π (σ (π ⟨Multiplicative.ofAdd x, hx⟩)) = π ⟨Multiplicative.ofAdd x, hx⟩ := hσ _
      have hmem := (hπ.2.2.2.2 ((⟨Multiplicative.ofAdd x, hx⟩ : Γ)⁻¹ *
        σ (π ⟨Multiplicative.ofAdd x, hx⟩))).mp (by rw [map_mul, map_inv, hy, inv_mul_cancel])
      have := hWinv (Multiplicative.ofAdd x) _ (hNsub hmem).1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this
      exact this
    · have : Multiplicative.ofAdd x ∉ tsupport h' := fun hh => hx (hUΓ (Or.inr hh))
      exact (image_eq_zero_of_notMem_tsupport this).symm
