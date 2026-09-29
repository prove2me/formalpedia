-- Prove2me | solution 1 for ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/91709067-1df1-51f4-9899-b791681b1afd

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charZero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open scoped MatrixGroups

namespace Char0Pen14

open ModularCurve

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]

abbrev ι (k K : Type*) [Field k] [Field K] [Algebra k K] : LaurentSeries k →+* LaurentSeries K :=
  coeffMap (algebraMap k K)

theorem ι_injective : Function.Injective (ι k K) := by
  intro x y h
  ext t
  have := congrArg (fun z => HahnSeries.coeff z t) h
  simpa [coeffMap_coeff] using this

theorem smul_ι (a : k) (x : LaurentSeries k) : algebraMap k K a • ι k K x = ι k K (a • x) := by
  ext t
  simp [coeffMap_coeff, Algebra.smul_def]

noncomputable def proj {σ : Type*} (ω : Module.Basis σ k K) (s : σ) : LaurentSeries K →ₗ[k] LaurentSeries k where
  toFun y :=
    { coeff := fun t => ω.repr (y.coeff t) s
      isPWO_support' := y.isPWO_support.mono (by
        intro t ht
        simp only [Function.mem_support, ne_eq] at ht ⊢
        intro h0
        apply ht
        rw [h0, map_zero, Finsupp.zero_apply]) }
  map_add' y z := by
    ext t
    simp
  map_smul' a y := by
    ext t
    simp [map_smul]

@[scoped simp] theorem proj_coeff {σ : Type*} (ω : Module.Basis σ k K) (s : σ) (y : LaurentSeries K) (t : ℤ) :
    (proj ω s y).coeff t = ω.repr (y.coeff t) s := rfl

theorem proj_smul_ι {σ : Type*} (ω : Module.Basis σ k K) (s : σ) (a : K) (x : LaurentSeries k) :
    proj ω s (a • ι k K x) = (ω.repr a s) • x := by
  ext t
  rw [proj_coeff, HahnSeries.coeff_smul, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul, mul_comm a,
    ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]

theorem proj_sum_basis_smul_ι {σ : Type*} (ω : Module.Basis σ k K) (S : Finset σ) (g : σ → LaurentSeries k) (s : σ) (hs : ∀ s ∉ S, g s = 0) :
    proj ω s (∑ s' ∈ S, ω s' • ι k K (g s')) = g s := by
  classical
  rw [map_sum]
  simp only [proj_smul_ι, Module.Basis.repr_self]
  by_cases h : s ∈ S
  · rw [Finset.sum_eq_single s]
    · simp
    · intro s' _ hne
      rw [Finsupp.single_apply, if_neg hne, zero_smul]
    · intro h'; exact absurd h h'
  · rw [hs s h]
    exact Finset.sum_eq_zero fun s' hs' => by
      rw [Finsupp.single_apply, if_neg (by rintro rfl; exact h hs'), zero_smul]

theorem eq_zero_of_sum_basis_smul_ι_eq_zero {σ : Type*} (ω : Module.Basis σ k K) (S : Finset σ) (g : σ → LaurentSeries k)
    (hs : ∀ s ∉ S, g s = 0) (h : ∑ s' ∈ S, ω s' • ι k K (g s') = 0) (s : σ) : g s = 0 := by
  rw [← proj_sum_basis_smul_ι ω S g s hs, h, map_zero]

theorem algebraMap_mul_eq_smul (a : K) (y : LaurentSeries K) : algebraMap K (LaurentSeries K) a * y = a • y := by
  rw [algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply, HahnSeries.C_mul_eq_smul]

theorem smul_mem_intermediateField (E : IntermediateField k (LaurentSeries k)) (c : k) {x : LaurentSeries k} (hx : x ∈ E) :
    c • x ∈ E := by
  rw [← algebraMap_mul_eq_smul]
  exact E.mul_mem (E.algebraMap_mem c) hx

theorem algebraMap_smul_eq (c : k) (z : LaurentSeries K) : algebraMap k K c • z = c • z := by
  ext t
  simp [Algebra.smul_def]

theorem smul_mul_assoc' (a : K) (x y : LaurentSeries K) : (a • x) * y = a • (x * y) := by
  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, mul_assoc]

section SpanStructure

variable (E : IntermediateField k (LaurentSeries k))

theorem closure_image_eq : (Submonoid.closure (ι k K '' (E : Set (LaurentSeries k))) : Set (LaurentSeries K)) = ι k K '' E := by
  let T : Submonoid (LaurentSeries K) := (E.toSubalgebra.toSubsemiring.toSubmonoid).map (ι k K : LaurentSeries k →* LaurentSeries K)
  have hT : (T : Set (LaurentSeries K)) = ι k K '' E := by
    ext x; simp [T]
  rw [← hT, Submonoid.closure_eq]

theorem exists_repr_of_mem_adjoin {σ : Type*} (ω : Module.Basis σ k K) {x : LaurentSeries K}
    (hx : x ∈ Algebra.adjoin K (ι k K '' (E : Set (LaurentSeries k)))) :
    ∃ (S : Finset σ) (g : σ → LaurentSeries k), (∀ s, g s ∈ E) ∧ (∀ s ∉ S, g s = 0) ∧
      x = ∑ s ∈ S, ω s • ι k K (g s) := by
  classical
  have hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin K (ι k K '' (E : Set (LaurentSeries k)))) := hx
  rw [Algebra.adjoin_eq_span, closure_image_eq] at hx'
  obtain ⟨f, T, hT, hfT, hsum⟩ := (@Submodule.mem_span_iff_exists_finset_subset K (LaurentSeries K) _ _ (_) _ x).mp hx'

  have hsum' : x = ∑ y ∈ T, f y • y := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Algebra.smul_def, algebraMap_mul_eq_smul]

  have hpre : ∀ y ∈ T, ∃ e ∈ E, ι k K e = y := fun y hy => by
    obtain ⟨e, he, rfl⟩ := hT hy; exact ⟨e, he, rfl⟩
  choose! pre hpreE hpreι using hpre
  set S := T.biUnion (fun y => (ω.repr (f y)).support) with hS
  refine ⟨S, fun s => ∑ y ∈ T, (ω.repr (f y) s) • pre y, ?_, ?_, ?_⟩
  · intro s
    exact E.sum_mem fun y hy => smul_mem_intermediateField E _ (hpreE y hy)
  · intro s hs
    refine Finset.sum_eq_zero fun y hy => ?_
    have : ω.repr (f y) s = 0 := by
      by_contra hne
      exact hs (Finset.mem_biUnion.mpr ⟨y, hy, Finsupp.mem_support_iff.mpr hne⟩)
    rw [this, zero_smul]
  · rw [hsum']

    have step : ∀ s, ω s • ι k K (∑ y ∈ T, (ω.repr (f y) s) • pre y) = ∑ y ∈ T, (ω s * algebraMap k K (ω.repr (f y) s)) • y := by
      intro s
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [← smul_ι, hpreι y hy, smul_smul]
    simp_rw [step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [← Finset.sum_smul]
    congr 1
    have hsub : (ω.repr (f y)).support ⊆ S := Finset.subset_biUnion_of_mem (fun y => (ω.repr (f y)).support) hy
    calc f y = Finsupp.linearCombination k ω (ω.repr (f y)) := (ω.linearCombination_repr (f y)).symm
      _ = ∑ s ∈ S, (ω.repr (f y) s) • ω s := by
          rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hsub]
          intro s _; exact zero_smul _ _
      _ = ∑ s ∈ S, ω s * algebraMap k K (ω.repr (f y) s) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Algebra.smul_def, mul_comm]

end SpanStructure

theorem mem_of_ι_mem_adjoin_image (E : IntermediateField k (LaurentSeries k)) (x₀ : LaurentSeries k)
    (h : ι k K x₀ ∈ IntermediateField.adjoin K (ι k K '' (E : Set (LaurentSeries k)))) : x₀ ∈ E := by
  classical
  obtain ⟨σ, ω⟩ : Σ σ : Type _, Module.Basis σ k K := ⟨_, Module.Basis.ofVectorSpace k K⟩
  obtain ⟨r, hr, s, hs, hxrs⟩ := IntermediateField.mem_adjoin_iff_div.mp h
  by_cases hs0 : s = 0
  · have : ι k K x₀ = 0 := by rw [hxrs, hs0, div_zero]
    have hx0 : x₀ = 0 := ι_injective (by rw [this, map_zero])
    rw [hx0]; exact E.zero_mem
  obtain ⟨Sr, g, hgE, hgS, hrrep⟩ := exists_repr_of_mem_adjoin E ω hr
  obtain ⟨Ss, hh, hhE, hhS, hsrep⟩ := exists_repr_of_mem_adjoin E ω hs
  set S := Sr ∪ Ss with hSdef
  have hrrep' : r = ∑ t ∈ S, ω t • ι k K (g t) := by
    rw [hrrep]; exact Finset.sum_subset Finset.subset_union_left fun t _ ht => by rw [hgS t ht, map_zero, smul_zero]
  have hsrep' : s = ∑ t ∈ S, ω t • ι k K (hh t) := by
    rw [hsrep]; exact Finset.sum_subset Finset.subset_union_right fun t _ ht => by rw [hhS t ht, map_zero, smul_zero]

  have hmul : ι k K x₀ * s = r := by
    rw [hxrs, div_mul_cancel₀ _ hs0]
  have hrel : ∑ t ∈ S, ω t • ι k K (x₀ * hh t - g t) = 0 := by
    have h1 : ι k K x₀ * s = ∑ t ∈ S, ω t • ι k K (x₀ * hh t) := by
      rw [hsrep', Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_mul, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, mul_left_comm]
    simp_rw [map_sub, smul_sub, Finset.sum_sub_distrib, ← h1, hmul, hrrep', sub_self]
  have hzero : ∀ t, x₀ * hh t - g t = 0 := fun t =>
    eq_zero_of_sum_basis_smul_ι_eq_zero ω S (fun t => x₀ * hh t - g t)
      (fun t ht => by
        show x₀ * hh t - g t = 0
        rw [hgS t (fun h' => ht (Finset.mem_union_left _ h')), hhS t (fun h' => ht (Finset.mem_union_right _ h')),
          mul_zero, sub_zero]) hrel t

  have hex : ∃ t, hh t ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hs0
    rw [hsrep']
    exact Finset.sum_eq_zero fun t _ => by rw [hall t, map_zero, smul_zero]
  obtain ⟨t, ht⟩ := hex
  have hx : x₀ = g t * (hh t)⁻¹ := by
    rw [← sub_eq_zero.mp (hzero t), mul_inv_cancel_right₀ ht]
  rw [hx]
  exact E.mul_mem (hgE t) (E.inv_mem (hhE t))

end Char0Pen14
p2m_reactivate "P2MW.S_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charZero.Char0Pen14"

theorem Char0Pen14.not_gammaH_bot_le_gamma0 (N d : ℕ) [NeZero N] [NeZero d] (hd : ¬ d ∣ N) :
    ¬ (CohCarrier.GammaH N ⊥ ≤ CongruenceSubgroup.Gamma0 d) := by
  intro hle
  let A : SL(2, ℤ) := ⟨!![1, 0; (N : ℤ), 1], by rw [Matrix.det_fin_two_of]; ring⟩
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    show (((N : ℤ) : ZMod N)) = 0
    rw [Int.cast_natCast, ZMod.natCast_self]
  have hA : A ∈ CohCarrier.GammaH N ⊥ := by
    refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
    rw [Subgroup.mem_bot]
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    show (((1 : ℤ) : ZMod N)) = 1
    rw [Int.cast_one]
  have hAd : A ∈ CongruenceSubgroup.Gamma0 d := hle hA
  rw [CongruenceSubgroup.Gamma0_mem] at hAd
  have : (((N : ℤ) : ZMod d)) = 0 := hAd
  rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff] at this
  exact hd this

open Char0Pen14 ModularCurve in

theorem solution
    (K : Type*) [Field K] [CharZero K] (N d : ℕ) [NeZero N] [NeZero d] (hd : ¬ d ∣ N) :
    ModularCurve.qExpand K d (ModularCurve.jqModC K) ∉ ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N ⊥) := by
  intro hK

  have hQ : qExpand ℚ d (jqModC ℚ) ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH N ⊥) := by
    apply mem_of_ι_mem_adjoin_image (K := K)
    rw [← qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC ℚ K (CohCarrier.GammaH N ⊥)]
    have hj : ι ℚ K (jqModC ℚ) = jqModC K := map_jqModC _
    rw [show ι ℚ K (qExpand ℚ d (jqModC ℚ)) = qExpand K d (jqModC K) by rw [coeffMap_qExpand, hj]]
    exact hK

  have hC : qExpand ℂ d (jqModC ℂ) ∈ qExpFunctionFieldC ℂ (CohCarrier.GammaH N ⊥) := by
    rw [qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC ℚ ℂ (CohCarrier.GammaH N ⊥)]
    have hj : coeffMap (algebraMap ℚ ℂ) (jqModC ℚ) = jqModC ℂ := map_jqModC _
    rw [show qExpand ℂ d (jqModC ℂ) = coeffMap (algebraMap ℚ ℂ) (qExpand ℚ d (jqModC ℚ)) by rw [coeffMap_qExpand, hj]]
    exact IntermediateField.subset_adjoin _ _ ⟨_, hQ, rfl⟩

  set Sset : Set (LaurentSeries ℂ) := {x : LaurentSeries ℂ | ∃ (k : ℤ)
      (f g : ModularForm (CohCarrier.GammaH N ⊥ : Subgroup (GL (Fin 2) ℝ)) k),
      UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
        x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)} with hSset
  have hsub : intFormRatiosC ℂ (CohCarrier.GammaH N ⊥) ⊆ Sset := by
    rintro x ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    have hf' : intSeriesC ℂ pf = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) := by
      rw [intSeriesC, hf]
    have hg' : intSeriesC ℂ pg = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) := by
      rw [intSeriesC, hg]
    refine ⟨k, f, g, ?_, by rw [hf', hg']⟩
    intro h0
    apply hg0
    rw [hg', h0, map_zero]
  have hle : qExpFunctionFieldC ℂ (CohCarrier.GammaH N ⊥) ≤ IntermediateField.adjoin ℂ Sset :=
    IntermediateField.adjoin.mono ℂ _ _ hsub
  have hjd : jqNModC ℂ d ∈ IntermediateField.adjoin ℂ Sset := hle hC

  have hT : ModularGroup.T ∈ CohCarrier.GammaH N ⊥ := by
    refine CohCarrier.mem_GammaH_iff.mpr ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma0_mem]
      show ((((ModularGroup.T : SL(2, ℤ)) 1 0 : ℤ) : ZMod N)) = 0
      rw [ModularGroup.T]; simp
    · rw [Subgroup.mem_bot]
      ext
      rw [CohCarrier.val_gamma0Units, Units.val_one]
      show ((((ModularGroup.T : SL(2, ℤ)) 1 1 : ℤ) : ZMod N)) = 1
      rw [ModularGroup.T]; simp
  have hbound := ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC (CohCarrier.GammaH N ⊥) hT d
  have hins : IntermediateField.adjoin ℂ (insert (jqNModC ℂ d) Sset) = IntermediateField.adjoin ℂ Sset := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff]
      exact ⟨hjd, IntermediateField.subset_adjoin ℂ _⟩
    · exact IntermediateField.adjoin.mono ℂ _ _ (Set.subset_insert _ _)
  rw [hins, IntermediateField.relrank_self] at hbound

  have hle1 : (CongruenceSubgroup.Gamma0 d).relIndex (CohCarrier.GammaH N ⊥) ≤ 1 := by exact_mod_cast hbound
  have hne0 : (CongruenceSubgroup.Gamma0 d).relIndex (CohCarrier.GammaH N ⊥) ≠ 0 :=
    Subgroup.FiniteIndex.index_ne_zero
  have heq1 : (CongruenceSubgroup.Gamma0 d).relIndex (CohCarrier.GammaH N ⊥) = 1 := by omega
  exact not_gammaH_bot_le_gamma0 N d hd (Subgroup.relIndex_eq_one.mp heq1)

end S_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charZero
end P2MW
export P2MW.S_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charZero (solution)
