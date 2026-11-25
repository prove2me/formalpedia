-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.exists_adelicNorm_vecMul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:42.326398+00:00
-- url     : https://prove2.me/submissions/87c48fcf-7d30-49a2-8a8d-6e8a4b08b9be

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
import Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_dirichlet_box
import Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_bound_infinite_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finite_mulSupport_max_one_norm
import Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_bound_finite_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_posIdele_infinite
import Theorems.Thm_GroundTheory_Automorphic_Reduction_posIdele_finite
import Theorems.Thm_GroundTheory_Automorphic_Reduction_ideleModule_posIdele
import Theorems.Thm_GroundTheory_Automorphic_Reduction_euclidNorm_two_le
import Theorems.Thm_GroundTheory_Automorphic_Reduction_adelicNorm_ratVec_single
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_diagonal_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_HasFiniteContent_finite_mulSupport
import Theorems.Thm_GroundTheory_Automorphic_Reduction_HasFiniteContent_vecMul
import Theorems.Thm_GroundTheory_Automorphic_Reduction_adelicNorm_smul
import Theorems.Thm_GroundTheory_Automorphic_Reduction_euclidNorm_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Reduction_eventually_norm_eq_one
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finEval_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_hasFiniteContent_ratVec
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infEval_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_le_one_of_mem
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


section
open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
namespace GroundTheory.Automorphic
noncomputable section
namespace Reduction
variable {K : Type*} [Field K] [NumberField K]
private theorem finprod_le_finprod_of_nonneg' {ι : Type*} {f g : ι → ℝ} (hf : (Function.mulSupport f).Finite)
    (hg : (Function.mulSupport g).Finite) (h0 : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i ≤ g i) :
    ∏ᶠ i, f i ≤ ∏ᶠ i, g i := by
  classical
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hf.toFinset ∪ hg.toFinset)
      (fun i hi => Finset.mem_coe.2 (Finset.mem_union_left _ (hf.mem_toFinset.2 hi))),
    finprod_eq_prod_of_mulSupport_subset g (s := hf.toFinset ∪ hg.toFinset)
      (fun i hi => Finset.mem_coe.2 (Finset.mem_union_right _ (hg.mem_toFinset.2 hi)))]
  exact Finset.prod_le_prod (fun i _ => h0 i) fun i _ => hfg i
end Reduction
end
end GroundTheory.Automorphic
end

set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (α δ : IdeleGroup K) (u : 𝔸[K]),
    ∃ x : Fin 2 → K, x ≠ 0 ∧ adelicNorm (ratVec x ᵥ* !![(α : 𝔸[K]), u; 0, (δ : 𝔸[K])]) ≤
      C * Real.sqrt (ideleModule K (α * δ) : ℝ) := by
  obtain ⟨D, hD, -, hxD⟩ := exists_isCompact_normOneSubgroup K
  obtain ⟨M, hM0, hM⟩ := exists_bound_infinite_of_isCompact hD
  obtain ⟨P, hP1, hP⟩ := exists_bound_finite_of_isCompact hD
  obtain ⟨B, hB, hbox⟩ := exists_dirichlet_box (K := K)
  set d := Module.finrank ℚ K with hd
  set A : ℝ := 3 * B * M + B with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max 1 (A ^ d * P), lt_of_lt_of_le one_pos (le_max_left _ _), fun α δ u => ?_⟩
  set r : IdeleGroup K := α * δ⁻¹ with hr
  have hr0 : 0 < (ideleModule K r : ℝ) := (ideleModule K r).2
  have hδ0 : 0 < (ideleModule K δ : ℝ) := (ideleModule K δ).2
  have hmod : (ideleModule K (α * δ) : ℝ) =
      (ideleModule K r : ℝ) * (ideleModule K δ : ℝ) ^ 2 := by
    have : α * δ = r * δ * δ := by rw [hr]; group
    rw [this, map_mul, map_mul]
    simp only [Positive.val_mul]
    ring
  by_cases hr1 : 1 ≤ (ideleModule K r : ℝ)
  · refine ⟨Pi.single 1 1, by simp, ?_⟩
    have hy : ratVec (Pi.single 1 1 : Fin 2 → K) ᵥ* !![(α : 𝔸[K]), u; 0, (δ : 𝔸[K])] =
        (δ : 𝔸[K]) • ratVec (Pi.single 1 1) := by
      ext i
      fin_cases i <;> simp [ratVec, vecMul, dotProduct, Fin.sum_univ_two]
    rw [hy, adelicNorm_smul (hasFiniteContent_ratVec (by simp)) δ, adelicNorm_ratVec_single,
      mul_one, hmod, Real.sqrt_mul hr0.le, Real.sqrt_sq hδ0.le]
    have h1 : 1 ≤ Real.sqrt (ideleModule K r : ℝ) := Real.one_le_sqrt.2 hr1
    calc (ideleModule K δ : ℝ) ≤ 1 * (Real.sqrt (ideleModule K r : ℝ) * ideleModule K δ) := by
          nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · rw [not_le] at hr1
    have hd0 : 0 < d := Module.finrank_pos
    set s : ℝ := (ideleModule K r : ℝ) ^ ((1 : ℝ) / (2 * d)) with hs
    have hs0 : 0 < s := Real.rpow_pos_of_pos hr0 _
    have hs1 : s < 1 := Real.rpow_lt_one hr0.le hr1 (by positivity)
    have hspow : s ^ (2 * d) = (ideleModule K r : ℝ) := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
      have : (1 : ℝ) / (2 * d) * ((2 * d : ℕ) : ℝ) = 1 := by
        push_cast
        field_simp
      rw [this, Real.rpow_one]
    set t : IdeleGroup K := posIdele (s ^ 2) (by positivity) with ht
    have htmod : (ideleModule K t : ℝ) = (ideleModule K r : ℝ) := by
      rw [ht, ideleModule_posIdele, ← pow_mul, hspow]
    have hnorm1 : r * t⁻¹ ∈ normOneSubgroup K := by
      change r * t⁻¹ ∈ (ideleModule K).ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
      exact Subtype.ext htmod.symm
    obtain ⟨μ, hμ⟩ := hxD _ hnorm1
    set σ : IdeleGroup K := diagonal K μ * (r * t⁻¹) with hσ
    set w' : 𝔸[K] := algebraMap K 𝔸[K] (μ : K) * u * ((δ⁻¹ : IdeleGroup K) : 𝔸[K]) with hw'
    set N : ℕ := ⌈1 / s⌉₊ with hN
    have hN0 : 0 < N := Nat.ceil_pos.2 (by positivity)
    obtain ⟨l, hl0, hlw, c, hcv, hcw⟩ := hbox w' N hN0
    have hlK : (l : K) ≠ 0 := (RingOfIntegers.coe_ne_zero_iff).2 hl0
    set L : 𝔸[K] := algebraMap K 𝔸[K] (l : K) with hL
    set z : Fin 2 → 𝔸[K] := ![L * (σ : 𝔸[K]) * (t : 𝔸[K]), L * w' + algebraMap K 𝔸[K] c] with hz
    refine ⟨![(μ : K) * l, c], ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp only [Matrix.cons_val_zero, Pi.zero_apply] at h0
      exact mul_ne_zero μ.ne_zero hlK h0
    have h1 : (δ : 𝔸[K]) * ((δ⁻¹ : IdeleGroup K) : 𝔸[K]) = 1 := Units.mul_inv δ
    have h2 : ((t⁻¹ : IdeleGroup K) : 𝔸[K]) * (t : 𝔸[K]) = 1 := Units.inv_mul t
    have hσ' : (σ : 𝔸[K]) = algebraMap K 𝔸[K] (μ : K) * (α : 𝔸[K]) *
        ((δ⁻¹ : IdeleGroup K) : 𝔸[K]) * ((t⁻¹ : IdeleGroup K) : 𝔸[K]) := by
      rw [hσ, hr, Units.val_mul, Units.val_mul, Units.val_mul, coe_diagonal]
      ring
    have hy : ratVec ![(μ : K) * l, c] ᵥ* !![(α : 𝔸[K]), u; 0, (δ : 𝔸[K])] = (δ : 𝔸[K]) • z := by
      funext i
      fin_cases i
      · simp only [ratVec, vecMul, dotProduct, Fin.sum_univ_two, hz, hσ', hL,
          Pi.smul_apply, smul_eq_mul]
        simp
        linear_combination (-(algebraMap K 𝔸[K] (μ : K) * algebraMap K 𝔸[K] (l : K) * (α : 𝔸[K]) *
          (((t⁻¹ : IdeleGroup K) : 𝔸[K]) * (t : 𝔸[K])))) * h1 -
          (algebraMap K 𝔸[K] (μ : K) * algebraMap K 𝔸[K] (l : K) * (α : 𝔸[K])) * h2
      · simp only [ratVec, vecMul, dotProduct, Fin.sum_univ_two, hz, hw', hL,
          Pi.smul_apply, smul_eq_mul]
        simp
        linear_combination (-(algebraMap K 𝔸[K] (μ : K) * algebraMap K 𝔸[K] (l : K) * u)) * h1

    have hLv : ∀ v : HeightOneSpectrum (𝓞 K), ‖L.2 v‖ ≤ 1 := fun v =>
      norm_le_one_of_mem v (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles K l v)
    have hz0v : ∀ v : HeightOneSpectrum (𝓞 K),
        ‖finComp v z 0‖ = ‖L.2 v‖ * ‖(σ : 𝔸[K]).2 v‖ := fun v => by
      simp only [finComp, hz, Matrix.cons_val_zero, adele_snd_mul_apply, norm_mul, ht,
        posIdele_finite, mul_one]
    have hz1v : ∀ v : HeightOneSpectrum (𝓞 K), ‖finComp v z 1‖ ≤ 1 := fun v => by
      simpa only [finComp, hz, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] using hcv v
    have hzc : HasFiniteContent z := by
      filter_upwards [GroundTheory.Global.IdeleGroup.eventually_norm_eq_one σ,
        Reduction.eventually_norm_eq_one hlK] with v hv1 hv2
      have h0 : ‖finComp v z 0‖ = 1 := by
        rw [hz0v, hv1, mul_one]
        exact hv2
      refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_)
        (h0 ▸ norm_le_pi_norm _ 0)
      fin_cases i
      · exact h0.le
      · exact hz1v v
    have hfinv : ∀ v : HeightOneSpectrum (𝓞 K), ‖finComp v z‖ ≤ max 1 ‖(σ : 𝔸[K]).2 v‖ := by
      intro v
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      fin_cases i
      · change ‖finComp v z 0‖ ≤ _
        rw [hz0v]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hLv v)).trans (le_max_right _ _)
      · exact (hz1v v).trans (le_max_left _ _)
    have hNl : 1 / s ≤ N := Nat.le_ceil _
    have hNu : (N : ℝ) < 1 / s + 1 := Nat.ceil_lt_add_one (by positivity)
    have hinf : ∀ w : InfinitePlace K, euclidNorm (infComp w z) ≤ A * s := by
      intro w
      refine (euclidNorm_two_le _).trans ?_
      have e0 : ‖infComp w z 0‖ = ‖L.1 w‖ * ‖(σ : 𝔸[K]).1 w‖ * s ^ 2 := by
        simp only [infComp, hz, Matrix.cons_val_zero, adele_fst_mul_apply, norm_mul, ht,
          norm_posIdele_infinite]
      have e1 : ‖infComp w z 1‖ ≤ B / N := by
        simpa only [infComp, hz, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] using hcw w
      have hLw : ‖L.1 w‖ ≤ (N + 1) * B := hlw w
      have hσw : ‖(σ : 𝔸[K]).1 w‖ ≤ M := hM σ hμ w
      have hN1 : ((N : ℝ) + 1) * s ^ 2 ≤ 3 * s := by
        have : ((N : ℝ) + 1) * s ^ 2 ≤ (1 / s + 2) * s ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        calc ((N : ℝ) + 1) * s ^ 2 ≤ (1 / s + 2) * s ^ 2 := this
          _ = s + 2 * s ^ 2 := by field_simp
          _ ≤ 3 * s := by nlinarith
      have hBN : B / N ≤ B * s := by
        calc B / N ≤ B / (1 / s) := div_le_div_of_nonneg_left hB.le (by positivity) hNl
          _ = B * s := by field_simp
      have hprod : ‖L.1 w‖ * ‖(σ : 𝔸[K]).1 w‖ * s ^ 2 ≤ 3 * B * M * s := by
        calc ‖L.1 w‖ * ‖(σ : 𝔸[K]).1 w‖ * s ^ 2 ≤ ((N + 1) * B) * M * s ^ 2 := by
              gcongr
          _ = B * M * (((N : ℝ) + 1) * s ^ 2) := by ring
          _ ≤ B * M * (3 * s) := mul_le_mul_of_nonneg_left hN1 (by positivity)
          _ = 3 * B * M * s := by ring
      rw [e0]
      calc ‖L.1 w‖ * ‖(σ : 𝔸[K]).1 w‖ * s ^ 2 + ‖infComp w z 1‖ ≤ 3 * B * M * s + B * s :=
            add_le_add hprod (e1.trans hBN)
        _ = A * s := by rw [hA]; ring
    have hzbound : adelicNorm z ≤ (A * s) ^ d * P := by
      rw [adelicNorm]
      refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _) (by positivity)
      · calc ∏ w : InfinitePlace K, euclidNorm (infComp w z) ^ w.mult
            ≤ ∏ w : InfinitePlace K, (A * s) ^ w.mult :=
              Finset.prod_le_prod (fun _ _ => pow_nonneg (euclidNorm_nonneg _) _) fun w _ =>
                pow_le_pow_left₀ (euclidNorm_nonneg _) (hinf w) _
          _ = (A * s) ^ d := by rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
      · calc ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖finComp v z‖
            ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 K), max 1 ‖(σ : 𝔸[K]).2 v‖ :=
              finprod_le_finprod_of_nonneg' hzc.finite_mulSupport (finite_mulSupport_max_one_norm σ)
                (fun _ => norm_nonneg _) hfinv
          _ ≤ P := hP σ hμ
    have hsq : Real.sqrt (ideleModule K r : ℝ) = s ^ d := by
      rw [← hspow, show s ^ (2 * d) = (s ^ d) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [hy, adelicNorm_smul hzc δ, hmod, Real.sqrt_mul hr0.le, Real.sqrt_sq hδ0.le, hsq]
    calc (ideleModule K δ : ℝ) * adelicNorm z ≤ (ideleModule K δ : ℝ) * ((A * s) ^ d * P) :=
          mul_le_mul_of_nonneg_left hzbound hδ0.le
      _ = (A ^ d * P) * (s ^ d * (ideleModule K δ : ℝ)) := by rw [mul_pow]; ring
      _ ≤ max 1 (A ^ d * P) * (s ^ d * (ideleModule K δ : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
end GroundTheory.Automorphic.Reduction
