-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.exists_dirichlet_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:58.684006+00:00
-- url     : https://prove2.me/submissions/4993c3e7-96ec-4317-8603-8f630dc3ec7d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_apply_le_norm_homeomorphMixedSpace
import Theorems.Thm_GroundTheory_Automorphic_Reduction_abs_sub_lt_one_of_floor_eq
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_le_one_of_mem_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_diagonal_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finEval_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infEval_apply
import Theorems.Thm_GroundTheory_Automorphic_RestrictedProduct_matrixUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_algebraMap_integers_mem_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Global_coe_integerEquivAdicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_exists_sub_mem_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Global_homeomorphMixedSpace_algebraMap
import Theorems.Thm_GroundTheory_Global_homeomorphMixedSpace_sub
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.AdelicGLn.diagonal_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.finAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.finEval_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infEval_apply
attribute [local simp] GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.coe_integerEquivAdicCompletionIntegers
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
open scoped Classical
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution : ∃ B : ℝ, 0 < B ∧ ∀ (a : 𝔸[K]) (N : ℕ), 0 < N →
    ∃ l : 𝓞 K, l ≠ 0 ∧
      (∀ w : InfinitePlace K, ‖(algebraMap K 𝔸[K] (l : K)).1 w‖ ≤ (N + 1) * B) ∧
      ∃ c : K, (∀ v : HeightOneSpectrum (𝓞 K),
          ‖(algebraMap K 𝔸[K] (l : K) * a + algebraMap K 𝔸[K] c).2 v‖ ≤ 1) ∧
        ∀ w : InfinitePlace K,
          ‖(algebraMap K 𝔸[K] (l : K) * a + algebraMap K 𝔸[K] c).1 w‖ ≤ B / N := by
  set bZ := RingOfIntegers.basis K
  set b := mixedEmbedding.latticeBasis K
  set B₁ : ℝ := ∑ i, ‖b i‖ with hB₁
  set B₂ : ℝ := ∑ w : InfinitePlace K, ∑ i, ‖(algebraMap K 𝔸[K] ((bZ i : 𝓞 K) : K)).1 w‖ with hB₂
  have hB₁0 : 0 ≤ B₁ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB₂0 : 0 ≤ B₂ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨B₁ + B₂ + 1, by positivity, fun a N hN => ?_⟩

  let lam : (Module.Free.ChooseBasisIndex ℤ (𝓞 K) → Fin (N + 1)) → 𝓞 K :=
    fun m => bZ.equivFun.symm fun i => ((m i : ℕ) : ℤ)
  have hlam_inj : Function.Injective lam := by
    intro m m' h
    have h' := bZ.equivFun.symm.injective h
    funext i
    exact Fin.ext (by exact_mod_cast congrFun h' i)

  have hk : ∀ l : 𝓞 K, ∃ k : K, (algebraMap K 𝔸[K] (l : K) * a).2 -
      algebraMap K (FiniteAdeleRing (𝓞 K) K) k ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K :=
    fun l => GroundTheory.Global.exists_sub_mem_integralFiniteAdeles _
  choose k hk using hk
  let e : 𝓞 K → 𝔸[K] := fun l => algebraMap K 𝔸[K] (l : K) * a - algebraMap K 𝔸[K] (k l)
  let s : 𝓞 K → Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ :=
    fun l i => b.repr (GroundTheory.Global.homeomorphMixedSpace K (e l).1) i
  have hbox : ∀ (l : 𝓞 K) i, ⌊(N : ℝ) * Int.fract (s l i)⌋₊ < N := fun l i => by
    refine (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg _))).2 ?_
    exact mul_lt_of_lt_one_right (by exact_mod_cast hN) (Int.fract_lt_one _)
  let box : 𝓞 K → Module.Free.ChooseBasisIndex ℤ (𝓞 K) → Fin N :=
    fun l i => ⟨⌊(N : ℝ) * Int.fract (s l i)⌋₊, hbox l i⟩
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K) → Fin N) <
      Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K) → Fin (N + 1)) := by
    have : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) := bZ.index_nonempty
    simp only [Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_lt_pow_left (Nat.lt_succ_self N) Fintype.card_ne_zero
  obtain ⟨m, m', hne, hmm⟩ := Fintype.exists_ne_map_eq_of_card_lt (box ∘ lam) hcard
  have hlamK : ∀ p, ((lam p : 𝓞 K) : K) = ∑ i, (((p i : ℕ) : ℤ) • ((bZ i : 𝓞 K) : K)) := by
    intro p
    change algebraMap (𝓞 K) K (bZ.equivFun.symm _) = _
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    simp
  refine ⟨lam m - lam m', sub_ne_zero.2 (hlam_inj.ne hne), ?_, ?_⟩
  · intro w
    let φ : K →+* w.Completion := (infEval w).comp (algebraMap K 𝔸[K])
    have hφ : ∀ x : K, (algebraMap K 𝔸[K] x).1 w = φ x := fun _ => rfl
    have hcast : ((lam m - lam m' : 𝓞 K) : K) =
        ∑ i, ((((m i : ℕ) : ℤ) - ((m' i : ℕ) : ℤ)) • ((bZ i : 𝓞 K) : K)) := by
      rw [show ((lam m - lam m' : 𝓞 K) : K) = (lam m : K) - (lam m' : K) from
        map_sub (algebraMap (𝓞 K) K) _ _, hlamK, hlamK, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
    have hz : ∀ i, ‖((((m i : ℕ) : ℤ) - ((m' i : ℕ) : ℤ)) : ℤ)‖ ≤ N := fun i => by
      have h1 := (m i).2
      have h2 := (m' i).2
      rw [Int.norm_eq_abs]
      have : |(((m i : ℕ) : ℤ) - ((m' i : ℕ) : ℤ))| ≤ (N : ℤ) := by
        rw [abs_le]; constructor <;> omega
      exact_mod_cast this
    rw [hφ, hcast, map_sum]
    calc ‖∑ i, φ ((((m i : ℕ) : ℤ) - ((m' i : ℕ) : ℤ)) • ((bZ i : 𝓞 K) : K))‖
        ≤ ∑ i, ‖φ ((((m i : ℕ) : ℤ) - ((m' i : ℕ) : ℤ)) • ((bZ i : 𝓞 K) : K))‖ := norm_sum_le _ _
      _ ≤ ∑ i, (N : ℝ) * ‖φ ((bZ i : 𝓞 K) : K)‖ := Finset.sum_le_sum fun i _ => by
          rw [map_zsmul]
          exact (norm_zsmul_le _ _).trans (mul_le_mul_of_nonneg_right (hz i) (norm_nonneg _))
      _ = N * ∑ i, ‖(algebraMap K 𝔸[K] ((bZ i : 𝓞 K) : K)).1 w‖ := by rw [Finset.mul_sum]; rfl
      _ ≤ N * B₂ := mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun w : InfinitePlace K =>
            ∑ i, ‖(algebraMap K 𝔸[K] ((bZ i : 𝓞 K) : K)).1 w‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ w))
          (Nat.cast_nonneg _)
      _ ≤ (N + 1) * (B₁ + B₂ + 1) := by
          have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
          nlinarith
  · set sm := s (lam m) with hsm
    set sm' := s (lam m') with hsm'
    let F : 𝓞 K := ∑ i, (⌊sm i⌋ - ⌊sm' i⌋) • bZ i
    have hE : algebraMap K 𝔸[K] ((lam m - lam m' : 𝓞 K) : K) * a +
        algebraMap K 𝔸[K] (-(k (lam m) - k (lam m')) - (F : K)) =
        e (lam m) - e (lam m') - algebraMap K 𝔸[K] (F : K) := by
      rw [show ((lam m - lam m' : 𝓞 K) : K) = (lam m : K) - (lam m' : K) from
        map_sub (algebraMap (𝓞 K) K) _ _]
      simp only [e, map_sub, map_neg, sub_mul]
      ring
    refine ⟨-(k (lam m) - k (lam m')) - (F : K), ?_, ?_⟩
    · intro v
      rw [hE]
      have hmem : (e (lam m) - e (lam m') - algebraMap K 𝔸[K] (F : K)).2 ∈
          GroundTheory.Global.integralFiniteAdeles (𝓞 K) K :=
        Subring.sub_mem _ (Subring.sub_mem _ (hk (lam m)) (hk (lam m')))
          (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles K F)
      exact norm_le_one_of_mem_integralFiniteAdeles hmem v
    · intro w
      rw [hE]
      refine (norm_apply_le_norm_homeomorphMixedSpace _ w).trans ?_
      have hb : ∀ i, mixedEmbedding K ((bZ i : 𝓞 K) : K) = b i := fun i => by
        rw [mixedEmbedding.latticeBasis_apply, integralBasis_apply]
      have hF : GroundTheory.Global.homeomorphMixedSpace K (algebraMap K 𝔸[K] (F : K)).1 =
          ∑ i, ((⌊sm i⌋ - ⌊sm' i⌋ : ℤ) : ℝ) • b i := by
        change GroundTheory.Global.homeomorphMixedSpace K (algebraMap K (InfiniteAdeleRing K) (F : K)) = _
        rw [GroundTheory.Global.homeomorphMixedSpace_algebraMap]
        change mixedEmbedding K (algebraMap (𝓞 K) K F) = _
        simp only [F, map_sum, map_zsmul, hb, Int.cast_smul_eq_zsmul]
      have hhom : GroundTheory.Global.homeomorphMixedSpace K
          (e (lam m) - e (lam m') - algebraMap K 𝔸[K] (F : K)).1 =
          ∑ i, (Int.fract (sm i) - Int.fract (sm' i)) • b i := by
        change GroundTheory.Global.homeomorphMixedSpace K ((e (lam m)).1 - (e (lam m')).1 -
          (algebraMap K 𝔸[K] (F : K)).1) = _
        rw [GroundTheory.Global.homeomorphMixedSpace_sub,
          GroundTheory.Global.homeomorphMixedSpace_sub, hF,
          ← b.sum_repr (GroundTheory.Global.homeomorphMixedSpace K (e (lam m)).1),
          ← b.sum_repr (GroundTheory.Global.homeomorphMixedSpace K (e (lam m')).1),
          ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← sub_smul, ← sub_smul]
        congr 1
        simp only [hsm, hsm', s, Int.fract]
        push_cast
        ring
      rw [hhom]
      have hclose : ∀ i, |Int.fract (sm i) - Int.fract (sm' i)| ≤ 1 / N := fun i => by
        have h := congrArg (fun f => ((f i : Fin N) : ℕ)) hmm
        simp only [Function.comp_apply, box] at h
        have h1 := abs_sub_lt_one_of_floor_eq
          (mul_nonneg (Nat.cast_nonneg N) (Int.fract_nonneg (sm i)))
          (mul_nonneg (Nat.cast_nonneg N) (Int.fract_nonneg (sm' i))) h
        rw [← mul_sub, abs_mul, Nat.abs_cast] at h1
        have hN' : (0 : ℝ) < N := by exact_mod_cast hN
        rw [le_div_iff₀ hN']
        linarith
      calc ‖∑ i, (Int.fract (sm i) - Int.fract (sm' i)) • b i‖
          ≤ ∑ i, ‖(Int.fract (sm i) - Int.fract (sm' i)) • b i‖ := norm_sum_le _ _
        _ ≤ ∑ i, 1 / (N : ℝ) * ‖b i‖ := Finset.sum_le_sum fun i _ => by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (hclose i) (norm_nonneg _)
        _ = B₁ / N := by rw [← Finset.mul_sum]; ring
        _ ≤ (B₁ + B₂ + 1) / N := by
            have hN' : (0 : ℝ) < N := by exact_mod_cast hN
            gcongr
            linarith
end GroundTheory.Automorphic.Reduction
