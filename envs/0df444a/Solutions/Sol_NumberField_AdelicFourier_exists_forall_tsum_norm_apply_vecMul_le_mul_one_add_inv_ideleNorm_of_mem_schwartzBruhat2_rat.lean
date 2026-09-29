-- Prove2me | solution 1 for NumberField.AdelicFourier.exists_forall_tsum_norm_apply_vecMul_le_mul_one_add_inv_ideleNorm_of_mem_schwartzBruhat2_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c12bb977-265d-536c-b0f5-a018837150ff

import Definitions.Def_AutomorphicForm_GodementSection
import Theorems.Thm_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_vecMul_le_mul_one_add_inv_ideleNorm_of_mem_schwartzBruhat2_rat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_vecMul_le_mul_one_add_inv_ideleNorm_of_mem_schwartzBruhat2_rat.NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_vecMul_le_mul_one_add_inv_ideleNorm_of_mem_schwartzBruhat2_rat.NumberField.AdelicFourier NumberField.TateGlobal AutomorphicForm IsDedekindDomain"

open scoped Classical

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mixedEmbedding.norm_apply InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp place mixedEmbedding InfiniteAdeleRing.ringEquiv_mixedSpace_apply InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace AdeleRing mixedEmbedding.norm mixedEmbedding.exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "pureTensorSet2 schwartzBruhat2 schwartzBruhat2_induction"
namespace ThetaBoundSol
p2m_open "NumberField.AdelicFourier NumberField"

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
theorem normAtPlace_ringEquiv_mixedSpace (w : InfinitePlace F) (x : InfiniteAdeleRing F) :
    normAtPlace w (InfiniteAdeleRing.ringEquiv_mixedSpace F x) = ‖x w‖ := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw]
    exact (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _
  · rw [normAtPlace_apply_of_isComplex hw]
    exact (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

theorem mixedEmbedding_norm_ringEquiv_mixedSpace (x : InfiniteAdeleRing F) :
    mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace F x) = ∏ w, ‖x w‖ ^ w.mult := by
  rw [mixedEmbedding.norm_apply]
  exact Finset.prod_congr rfl fun w _ => by rw [normAtPlace_ringEquiv_mixedSpace]

theorem ideleNorm_eq_mixedEmbedding_norm_of_snd_eq_one (a : (AdeleRing (𝓞 F) F)ˣ)
    (ha : (a : AdeleRing (𝓞 F) F).2 = 1) :
    ideleNorm F a
      = mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace F (a : AdeleRing (𝓞 F) F).1) := by
  rw [mixedEmbedding_norm_ringEquiv_mixedSpace, ideleNorm]
  exact NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one F a ha

theorem norm_ringEquiv_mixedSpace_le (x : InfiniteAdeleRing F) :
    ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ ≤ ∑ w, ‖x w‖ := by
  rw [norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [normAtPlace_ringEquiv_mixedSpace]
  exact Finset.single_le_sum (f := fun w => ‖x w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)

def fstHom (F : Type) [Field F] [NumberField F] : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F :=
  RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

def sndHom (F : Type) [Field F] [NumberField F] :
    AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F :=
  RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

theorem fstHom_apply (x : AdeleRing (𝓞 F) F) : fstHom F x = x.1 := rfl

theorem sndHom_apply (x : AdeleRing (𝓞 F) F) : sndHom F x = x.2 := rfl

def archHom (F : Type) [Field F] [NumberField F] : AdeleRing (𝓞 F) F →+* mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (fstHom F)

theorem archHom_apply (x : AdeleRing (𝓞 F) F) :
    archHom F x = InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 := rfl

theorem algebraMap_snd (ξ : F) :
    (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 = algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ := rfl

theorem archHom_algebraMap (ξ : F) :
    archHom F (algebraMap F (AdeleRing (𝓞 F) F) ξ) = mixedEmbedding F ξ := by
  rw [archHom_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

def rowVec (x a b : AdeleRing (𝓞 F) F) (ξ : Fin 2 → F) : Fin 2 → AdeleRing (𝓞 F) F :=
  ![a * algebraMap F (AdeleRing (𝓞 F) F) (ξ 0),
    b * (algebraMap F (AdeleRing (𝓞 F) F) (ξ 0) * x + algebraMap F (AdeleRing (𝓞 F) F) (ξ 1))]

def archRow (X A B : mixedSpace F) (ξ : Fin 2 → F) : Fin 2 → mixedSpace F :=
  ![A * mixedEmbedding F (ξ 0), B * (mixedEmbedding F (ξ 0) * X + mixedEmbedding F (ξ 1))]

def finRow (xf : FiniteAdeleRing (𝓞 F) F) (ξ : Fin 2 → F) : Fin 2 → FiniteAdeleRing (𝓞 F) F :=
  ![algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ 0),
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ 0) * xf + algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ 1)]

def archMat (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (mixedSpace F) :=
  m.map (archHom F)

def finMat (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
  m.map (sndHom F)

omit [NumberField F] in
theorem archRow_zero (X A B : mixedSpace F) (ξ : Fin 2 → F) :
    archRow X A B ξ 0 = A * mixedEmbedding F (ξ 0) := rfl

omit [NumberField F] in
theorem archRow_one (X A B : mixedSpace F) (ξ : Fin 2 → F) :
    archRow X A B ξ 1 = B * (mixedEmbedding F (ξ 0) * X + mixedEmbedding F (ξ 1)) := rfl

theorem finRow_zero (xf : FiniteAdeleRing (𝓞 F) F) (ξ : Fin 2 → F) :
    finRow xf ξ 0 = algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ 0) := rfl

theorem finRow_one (xf : FiniteAdeleRing (𝓞 F) F) (ξ : Fin 2 → F) :
    finRow xf ξ 1 = algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ 0) * xf
      + algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ 1) := rfl

theorem archHom_comp_rowVec (x a b : AdeleRing (𝓞 F) F) (ξ : Fin 2 → F) :
    (archHom F) ∘ rowVec x a b ξ = archRow (archHom F x) (archHom F a) (archHom F b) ξ := by
  funext j
  fin_cases j
  · simp [rowVec, archRow, map_mul, archHom_algebraMap]
  · simp [rowVec, archRow, map_mul, map_add, archHom_algebraMap]

theorem sndHom_comp_rowVec (x a b : AdeleRing (𝓞 F) F) (ha : a.2 = 1) (hb : b.2 = 1)
    (ξ : Fin 2 → F) : (sndHom F) ∘ rowVec x a b ξ = finRow x.2 ξ := by
  funext j
  fin_cases j
  · simp [rowVec, finRow, map_mul, sndHom_apply, ha, algebraMap_snd]
  · simp [rowVec, finRow, map_mul, map_add, sndHom_apply, hb, algebraMap_snd]

theorem arch_reading (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) (x a b : AdeleRing (𝓞 F) F)
    (ξ : Fin 2 → F) :
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (Matrix.vecMul (rowVec x a b ξ) m i).1)
      = Matrix.vecMul (archRow (archHom F x) (archHom F a) (archHom F b) ξ) (archMat m) := by
  funext i
  have h := RingHom.map_vecMul (archHom F) m (rowVec x a b ξ) i
  rw [archHom_apply] at h
  rw [h, archHom_comp_rowVec]
  rfl

theorem fin_reading (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) (x a b : AdeleRing (𝓞 F) F)
    (ha : a.2 = 1) (hb : b.2 = 1) (ξ : Fin 2 → F) :
    (fun i => (Matrix.vecMul (rowVec x a b ξ) m i).2) = Matrix.vecMul (finRow x.2 ξ) (finMat m) := by
  funext i
  have h := RingHom.map_vecMul (sndHom F) m (rowVec x a b ξ) i
  rw [sndHom_apply] at h
  rw [h, sndHom_comp_rowVec x a b ha hb]
  rfl

theorem norm_vecMul_le (u : Fin 2 → mixedSpace F) (M : Matrix (Fin 2) (Fin 2) (mixedSpace F)) :
    ‖Matrix.vecMul u M‖ ≤ ‖u‖ * ∑ i, ∑ j, ‖M i j‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have hj : Matrix.vecMul u M j = ∑ i, u i * M i j := rfl
  rw [hj]
  calc ‖∑ i, u i * M i j‖ ≤ ∑ i, ‖u i * M i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖u‖ * ‖M i j‖ := Finset.sum_le_sum fun i _ =>
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_le_pi_norm u i) (norm_nonneg _))
    _ = ‖u‖ * ∑ i, ‖M i j‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖u‖ * ∑ i, ∑ j, ‖M i j‖ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (norm_nonneg _)
        exact Finset.single_le_sum (f := fun j => ‖M i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)

def entryBound (m : AdelicGL2 (𝓞 F) F) : ℝ :=
  ∑ i, ∑ j, ∑ w : InfinitePlace F,
    ‖(((m⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w‖

theorem entryBound_nonneg (m : AdelicGL2 (𝓞 F) F) : 0 ≤ entryBound m := by
  unfold entryBound
  positivity

theorem continuous_entryBound : Continuous (entryBound (F := F)) := by
  unfold entryBound
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun w _ => ?_
  have h1 : Continuous fun m : AdelicGL2 (𝓞 F) F =>
      (((m⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) :=
    Units.continuous_coe_inv.matrix_elem i j
  exact ((continuous_apply w).comp h1.fst).norm

theorem archMat_mul_archMat_inv (m : AdelicGL2 (𝓞 F) F) :
    archMat (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * archMat ((m⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = 1 := by
  unfold archMat
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finMat_mul_finMat_inv (m : AdelicGL2 (𝓞 F) F) :
    finMat (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * finMat ((m⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = 1 := by
  unfold finMat
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem norm_le_entryBound_mul (m : AdelicGL2 (𝓞 F) F) (u : Fin 2 → mixedSpace F) :
    ‖u‖ ≤ entryBound m
      * ‖Matrix.vecMul u (archMat (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖ := by
  set u' := Matrix.vecMul u (archMat (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) with hu'
  have hu : u = Matrix.vecMul u'
      (archMat ((m⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) := by
    rw [hu', Matrix.vecMul_vecMul, archMat_mul_archMat_inv, Matrix.vecMul_one]
  calc ‖u‖ = ‖Matrix.vecMul u'
        (archMat ((m⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖ := by
          rw [← hu]
    _ ≤ ‖u'‖ * ∑ i, ∑ j,
          ‖archMat ((m⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j‖ :=
          norm_vecMul_le _ _
    _ ≤ ‖u'‖ * entryBound m := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          unfold entryBound
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          exact norm_ringEquiv_mixedSpace_le _
    _ = entryBound m * ‖u'‖ := mul_comm _ _

theorem exists_entryBound_le {K : Set (AdelicGL2 (𝓞 F) F)} (hK : IsCompact K) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ m ∈ K, entryBound m ≤ β := by
  obtain ⟨β, hβ⟩ := hK.exists_bound_of_continuousOn (continuous_entryBound (F := F)).continuousOn
  refine ⟨max β 0, le_max_right _ _, fun m hm => ?_⟩
  have h := hβ m hm
  rw [Real.norm_eq_abs] at h
  exact ((le_abs_self _).trans h).trans (le_max_left _ _)

theorem schwartz_decay (g : SchwartzMap (Fin 2 → mixedSpace F) ℂ) (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : Fin 2 → mixedSpace F, (1 + ‖y‖) ^ k * ‖g y‖ ≤ D := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) g, ?_, fun y => ?_⟩
  · have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl g 0
    rw [norm_iteratedFDeriv_zero] at h
    exact le_trans (by positivity) h
  · have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl g y
    rw [norm_iteratedFDeriv_zero] at h
    exact h

theorem arch_majorant (g : SchwartzMap (Fin 2 → mixedSpace F) ℂ) {K : Set (AdelicGL2 (𝓞 F) F)}
    (hK : IsCompact K) (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ m ∈ K, ∀ u : Fin 2 → mixedSpace F,
      ‖g (Matrix.vecMul u (archMat (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))‖
        ≤ D * ((1 + ‖u 0‖) ^ k)⁻¹ * ((1 + ‖u 1‖) ^ k)⁻¹ := by
  obtain ⟨β, hβ0, hβ⟩ := exists_entryBound_le hK
  obtain ⟨D₀, hD₀, hdec⟩ := schwartz_decay g (2 * k)
  refine ⟨D₀ * (1 + β) ^ (2 * k), by positivity, fun m hm u => ?_⟩
  set y := Matrix.vecMul u (archMat (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) with hy
  have hu : ‖u‖ ≤ β * ‖y‖ :=
    (norm_le_entryBound_mul m u).trans (mul_le_mul_of_nonneg_right (hβ m hm) (norm_nonneg _))
  have h1 : 1 + ‖u‖ ≤ (1 + β) * (1 + ‖y‖) := by nlinarith [norm_nonneg y, norm_nonneg u]
  have h2 : (1 + ‖u‖) ^ (2 * k) ≤ (1 + β) ^ (2 * k) * (1 + ‖y‖) ^ (2 * k) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 _
  have h3 : (1 + ‖u 0‖) ^ k * (1 + ‖u 1‖) ^ k ≤ (1 + ‖u‖) ^ (2 * k) := by
    rw [two_mul, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith [norm_le_pi_norm u 0]) _)
      (pow_le_pow_left₀ (by positivity) (by linarith [norm_le_pi_norm u 1]) _)
      (by positivity) (by positivity)
  have h4 : (1 + ‖u 0‖) ^ k * (1 + ‖u 1‖) ^ k * ‖g y‖ ≤ D₀ * (1 + β) ^ (2 * k) := by
    calc (1 + ‖u 0‖) ^ k * (1 + ‖u 1‖) ^ k * ‖g y‖
        ≤ (1 + ‖u‖) ^ (2 * k) * ‖g y‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ ≤ ((1 + β) ^ (2 * k) * (1 + ‖y‖) ^ (2 * k)) * ‖g y‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = (1 + β) ^ (2 * k) * ((1 + ‖y‖) ^ (2 * k) * ‖g y‖) := by ring
      _ ≤ (1 + β) ^ (2 * k) * D₀ := mul_le_mul_of_nonneg_left (hdec y) (by positivity)
      _ = D₀ * (1 + β) ^ (2 * k) := mul_comm _ _
  have hp0 : 0 < (1 + ‖u 0‖) ^ k := by positivity
  have hp1 : 0 < (1 + ‖u 1‖) ^ k := by positivity
  rw [mul_assoc, ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (mul_pos hp0 hp1)]
  calc ‖g y‖ * ((1 + ‖u 0‖) ^ k * (1 + ‖u 1‖) ^ k)
      = (1 + ‖u 0‖) ^ k * (1 + ‖u 1‖) ^ k * ‖g y‖ := by ring
    _ ≤ D₀ * (1 + β) ^ (2 * k) := h4

theorem exists_ringOfIntegers_eq_mul_of_forall_mem (s : 𝓞 F) (y : F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F),
      (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s * algebraMap F (FiniteAdeleRing (𝓞 F) F) y) v
        ∈ v.adicCompletionIntegers F) :
    ∃ c : 𝓞 F, (c : F) = (s : F) * y := by
  have h' : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ((s : F) * y) ≤ 1 := by
    intro v
    have hv := h v
    have he : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s * algebraMap F (FiniteAdeleRing (𝓞 F) F) y
        = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((s : F) * y) := by
      rw [map_mul]
      rfl
    rw [he] at hv
    change (((s : F) * y : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F at hv
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F ((s : F) * y) h'
  exact ⟨c, hc⟩

theorem finite_confinement (hf : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (hcs : HasCompactSupport hf)
    {K : Set (AdelicGL2 (𝓞 F) F)} (hK : IsCompact K) :
    ∃ s : 𝓞 F, s ≠ 0 ∧ ∃ W : Set (FiniteAdeleRing (𝓞 F) F),
      (∀ m ∈ K, ∀ w : Fin 2 → FiniteAdeleRing (𝓞 F) F,
        hf (Matrix.vecMul w (finMat (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))) ≠ 0 →
          (∀ v : HeightOneSpectrum (𝓞 F),
            (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s * w 0) v ∈ v.adicCompletionIntegers F)
          ∧ w 1 ∈ W) ∧
      (∀ y ∈ W, ∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s * y) v ∈ v.adicCompletionIntegers F) ∧
      (∀ y ∈ W, ∀ z ∈ W, ∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s * (y - z)) v ∈ v.adicCompletionIntegers F) := by

  let Θ : (Fin 2 → FiniteAdeleRing (𝓞 F) F) × AdelicGL2 (𝓞 F) F → (Fin 2 → FiniteAdeleRing (𝓞 F) F) :=
    fun p => Matrix.vecMul p.1
      (finMat ((p.2⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
  have hΘ : Continuous Θ := by
    refine continuous_pi fun j => ?_
    change Continuous fun p : (Fin 2 → FiniteAdeleRing (𝓞 F) F) × AdelicGL2 (𝓞 F) F =>
      ∑ i, p.1 i * (((p.2⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
    refine continuous_finsetSum _ fun i _ => ?_
    refine ((continuous_apply i).comp continuous_fst).mul ?_
    have h1 : Continuous fun p : (Fin 2 → FiniteAdeleRing (𝓞 F) F) × AdelicGL2 (𝓞 F) F =>
        (((p.2⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) :=
      (Units.continuous_coe_inv.comp continuous_snd).matrix_elem i j
    exact h1.snd
  let Ω : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F) := Θ '' (tsupport hf ×ˢ K)
  have hΩ : IsCompact Ω := ((show IsCompact (tsupport hf) from hcs).prod hK).image hΘ
  let Ω₀ : Set (FiniteAdeleRing (𝓞 F) F) := (fun w : Fin 2 → FiniteAdeleRing (𝓞 F) F => w 0) '' Ω
  let Ω₁ : Set (FiniteAdeleRing (𝓞 F) F) := (fun w : Fin 2 → FiniteAdeleRing (𝓞 F) F => w 1) '' Ω
  have hΩ₀ : IsCompact Ω₀ := hΩ.image (continuous_apply 0)
  have hΩ₁ : IsCompact Ω₁ := hΩ.image (continuous_apply 1)
  let D : Set (FiniteAdeleRing (𝓞 F) F) :=
    (fun p : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F => p.1 - p.2) '' (Ω₁ ×ˢ Ω₁)
  have hD : IsCompact D := (hΩ₁.prod hΩ₁).image (continuous_fst.sub continuous_snd)
  have hC : IsCompact (Ω₀ ∪ (Ω₁ ∪ D)) := hΩ₀.union (hΩ₁.union hD)
  obtain ⟨s, hs0, hs⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
      (𝓞 F) F hC
  refine ⟨s, hs0, Ω₁, fun m hm w hw => ?_, fun y hy v => hs y (Or.inr (Or.inl hy)) v,
    fun y hy z hz v => hs (y - z) (Or.inr (Or.inr ⟨(y, z), ⟨hy, hz⟩, rfl⟩)) v⟩

  have hwΩ : w ∈ Ω := by
    refine ⟨(Matrix.vecMul w (finMat (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))), m),
      ⟨subset_tsupport _ (Function.mem_support.2 hw), hm⟩, ?_⟩
    change Matrix.vecMul (Matrix.vecMul w (finMat (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))
      (finMat ((m⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) = w
    rw [Matrix.vecMul_vecMul, finMat_mul_finMat_inv, Matrix.vecMul_one]
  exact ⟨fun v => hs (w 0) (Or.inl ⟨w, hwΩ, rfl⟩) v, ⟨w, hwΩ, rfl⟩⟩

def rhsN (N : ℕ) (α β : ℝ) : ℝ :=
  (1 + α⁻¹) * (1 + β⁻¹) * (min 1 (α⁻¹ ^ N) + min 1 (β⁻¹ ^ N))

theorem rhsN_nonneg (N : ℕ) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : 0 ≤ rhsN N α β := by
  unfold rhsN
  have h1 : 0 ≤ min 1 (α⁻¹ ^ N) := le_min zero_le_one (by positivity)
  have h2 : 0 ≤ min 1 (β⁻¹ ^ N) := le_min zero_le_one (by positivity)
  positivity

theorem tensor_apply_rowVec (g : SchwartzMap (Fin 2 → mixedSpace F) ℂ)
    (hf : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    (x a b : AdeleRing (𝓞 F) F) (ha : a.2 = 1) (hb : b.2 = 1) (ξ : Fin 2 → F) :
    (fun v : Fin 2 → AdeleRing (𝓞 F) F =>
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (v i).1) * hf (fun i => (v i).2))
      (Matrix.vecMul (rowVec x a b ξ) m)
      = g (Matrix.vecMul (archRow (archHom F x) (archHom F a) (archHom F b) ξ) (archMat m))
        * hf (Matrix.vecMul (finRow x.2 ξ) (finMat m)) := by
  show g _ * hf _ = _
  rw [arch_reading, fin_reading m x a b ha hb]

def FinBound (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (K : Set (AdelicGL2 (𝓞 F) F)) (N : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ m ∈ K, ∀ (x : AdeleRing (𝓞 F) F) (a b : (AdeleRing (𝓞 F) F)ˣ),
    (a : AdeleRing (𝓞 F) F).2 = 1 → (b : AdeleRing (𝓞 F) F).2 = 1 →
    ∀ T : Finset (Fin 2 → F), (∀ ξ ∈ T, ξ ≠ 0) →
      ∑ ξ ∈ T, ‖Φ (Matrix.vecMul (rowVec x a b ξ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖
        ≤ C * rhsN N (ideleNorm F a) (ideleNorm F b)

theorem finBound_tensor (g : SchwartzMap (Fin 2 → mixedSpace ℚ) ℂ)
    (hf : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ) (hlc : IsLocallyConstant hf)
    (hcs : HasCompactSupport hf) {K : Set (AdelicGL2 (𝓞 ℚ) ℚ)} (hK : IsCompact K) (N : ℕ) :
    FinBound (fun v : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace ℚ (v i).1) * hf (fun i => (v i).2)) K N := by
  obtain ⟨s, hs0, W, hW1, hW2, hW3⟩ := finite_confinement hf hcs hK
  obtain ⟨M, C, hC0, hK3b⟩ :=
    NumberField.mixedEmbedding.exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat
      hs0 N
  obtain ⟨D, hD0, hD⟩ := arch_majorant g hK M
  obtain ⟨H₀, hH₀⟩ := hlc.continuous.bounded_above_of_compact_support hcs
  have hH0 : 0 ≤ max H₀ 0 := le_max_right _ _
  have hHb : ∀ w, ‖hf w‖ ≤ max H₀ 0 := fun w => (hH₀ w).trans (le_max_left _ _)
  refine ⟨D * max H₀ 0 * C, by positivity, fun m hm x a b ha hb T hT => ?_⟩

  set A : mixedSpace ℚ := archHom ℚ (a : AdeleRing (𝓞 ℚ) ℚ) with hA
  set B : mixedSpace ℚ := archHom ℚ (b : AdeleRing (𝓞 ℚ) ℚ) with hB
  set X : mixedSpace ℚ := archHom ℚ x with hX
  set xf : FiniteAdeleRing (𝓞 ℚ) ℚ := x.2 with hxf
  set mM : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
    (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) with hmM
  have hNA : mixedEmbedding.norm A = ideleNorm ℚ a := by
    rw [hA, archHom_apply, ← ideleNorm_eq_mixedEmbedding_norm_of_snd_eq_one a ha]
  have hNB : mixedEmbedding.norm B = ideleNorm ℚ b := by
    rw [hB, archHom_apply, ← ideleNorm_eq_mixedEmbedding_norm_of_snd_eq_one b hb]
  have hApos : 0 < mixedEmbedding.norm A := hNA ▸ ideleNorm_pos a
  have hBpos : 0 < mixedEmbedding.norm B := hNB ▸ ideleNorm_pos b

  let η : ℚ → ℚ := fun ξ₀ =>
    if hh : ξ₀ ≠ 0 ∧ ∃ y : ℚ, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ξ₀ * xf
        + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) y ∈ W then hh.2.choose else 0
  have hη0 : η 0 = 0 := by
    show (if hh : (0 : ℚ) ≠ 0 ∧ _ then _ else _) = 0
    rw [dif_neg (fun hh => hh.1 rfl)]
  have hηW : ∀ ξ₀ : ℚ, ξ₀ ≠ 0 → ∀ y : ℚ,
      algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ξ₀ * xf + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) y ∈ W →
      algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ξ₀ * xf
        + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (η ξ₀) ∈ W := by
    intro ξ₀ hξ y hy
    have hh : ξ₀ ≠ 0 ∧ ∃ y : ℚ, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ξ₀ * xf
        + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) y ∈ W := ⟨hξ, y, hy⟩
    have hdef : η ξ₀ = hh.2.choose := dif_pos hh
    rw [hdef]
    exact hh.2.choose_spec

  let τ : ℚ → mixedSpace ℚ := fun ξ₀ => B * (mixedEmbedding ℚ ξ₀ * X + mixedEmbedding ℚ (η ξ₀))
  have hτ0 : τ 0 = 0 := by
    show B * (mixedEmbedding ℚ 0 * X + mixedEmbedding ℚ (η 0)) = 0
    rw [hη0, map_zero, zero_mul, zero_add, mul_zero]

  let ker : ℚ × ℚ → ℝ := fun p =>
    ((1 + ‖A * mixedEmbedding ℚ p.1‖) ^ M)⁻¹ * ((1 + ‖τ p.1 + B * mixedEmbedding ℚ p.2‖) ^ M)⁻¹
  let e : (Fin 2 → ℚ) → ℚ × ℚ := fun ξ => (ξ 0, ξ 1 - η (ξ 0))
  have he : Function.Injective e := by
    intro ξ ξ' hξ
    have h0 : ξ 0 = ξ' 0 := congrArg Prod.fst hξ
    have h1 : ξ 1 - η (ξ 0) = ξ' 1 - η (ξ' 0) := congrArg Prod.snd hξ
    rw [h0, sub_left_inj] at h1
    funext i
    fin_cases i
    exacts [h0, h1]
  have hker : ∀ ξ : Fin 2 → ℚ, ker (e ξ)
      = ((1 + ‖archRow X A B ξ 0‖) ^ M)⁻¹ * ((1 + ‖archRow X A B ξ 1‖) ^ M)⁻¹ := by
    intro ξ
    have h1 : τ (ξ 0) + B * mixedEmbedding ℚ (ξ 1 - η (ξ 0)) = archRow X A B ξ 1 := by
      rw [archRow_one, map_sub]
      show B * (mixedEmbedding ℚ (ξ 0) * X + mixedEmbedding ℚ (η (ξ 0)))
        + B * (mixedEmbedding ℚ (ξ 1) - mixedEmbedding ℚ (η (ξ 0))) = _
      ring
    show ((1 + ‖A * mixedEmbedding ℚ (ξ 0)‖) ^ M)⁻¹
        * ((1 + ‖τ (ξ 0) + B * mixedEmbedding ℚ (ξ 1 - η (ξ 0))‖) ^ M)⁻¹ = _
    rw [h1, archRow_zero]

  let Tf : Finset (Fin 2 → ℚ) := T.filter fun ξ => hf (Matrix.vecMul (finRow xf ξ) (finMat mM)) ≠ 0

  have hterm : ∀ ξ ∈ Tf,
      ‖g (Matrix.vecMul (archRow X A B ξ) (archMat mM))‖ * ‖hf (Matrix.vecMul (finRow xf ξ) (finMat mM))‖
        ≤ (D * max H₀ 0) * ker (e ξ) := by
    intro ξ _
    have hg := hD m hm (archRow X A B ξ)
    rw [hker]
    calc ‖g (Matrix.vecMul (archRow X A B ξ) (archMat mM))‖
          * ‖hf (Matrix.vecMul (finRow xf ξ) (finMat mM))‖
        ≤ (D * ((1 + ‖archRow X A B ξ 0‖) ^ M)⁻¹ * ((1 + ‖archRow X A B ξ 1‖) ^ M)⁻¹) * max H₀ 0 :=
          mul_le_mul hg (hHb _) (norm_nonneg _) (by positivity)
      _ = D * max H₀ 0 * (((1 + ‖archRow X A B ξ 0‖) ^ M)⁻¹ * ((1 + ‖archRow X A B ξ 1‖) ^ M)⁻¹) := by
          ring

  have hmem : ∀ p ∈ Tf.image e, p ≠ 0 ∧ (∃ c : 𝓞 ℚ, (c : ℚ) = (s : ℚ) * p.1) ∧
      (∃ c : 𝓞 ℚ, (c : ℚ) = (s : ℚ) * p.2) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨ξ, hξ, rfl⟩ := hp
    rw [Finset.mem_filter] at hξ
    obtain ⟨hξT, hne⟩ := hξ
    have hξ0 : ξ ≠ 0 := hT ξ hξT
    obtain ⟨hint0, hWξ⟩ := hW1 m hm (finRow xf ξ) hne
    refine ⟨fun h0 => hξ0 ?_, exists_ringOfIntegers_eq_mul_of_forall_mem s (ξ 0) hint0, ?_⟩
    · have h01 : ξ 0 = 0 := congrArg Prod.fst h0
      have h02 : ξ 1 - η (ξ 0) = 0 := congrArg Prod.snd h0
      rw [h01, hη0, sub_zero] at h02
      funext i
      fin_cases i
      exacts [h01, h02]
    · show ∃ c : 𝓞 ℚ, (c : ℚ) = (s : ℚ) * (ξ 1 - η (ξ 0))
      by_cases hz : ξ 0 = 0
      · rw [hz, hη0, sub_zero]
        refine exists_ringOfIntegers_eq_mul_of_forall_mem s (ξ 1) fun v => ?_
        have hv := hW2 _ hWξ v
        have hf1 : finRow xf ξ 1 = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1) := by
          rw [finRow_one, hz, map_zero, zero_mul, zero_add]
        rwa [hf1] at hv
      · have hWη := hηW (ξ 0) hz (ξ 1) hWξ
        refine exists_ringOfIntegers_eq_mul_of_forall_mem s (ξ 1 - η (ξ 0)) fun v => ?_
        have hv := hW3 _ hWξ _ hWη v
        have hdiff : finRow xf ξ 1 - (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * xf
            + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (η (ξ 0)))
            = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1 - η (ξ 0)) := by
          rw [finRow_one, map_sub]
          ring
        rwa [hdiff] at hv

  have h4 : ∑ p ∈ Tf.image e, ker p ≤ C * (1 + (mixedEmbedding.norm A)⁻¹)
      * (1 + (mixedEmbedding.norm B)⁻¹)
      * (min 1 ((mixedEmbedding.norm A)⁻¹ ^ N) + min 1 ((mixedEmbedding.norm B)⁻¹ ^ N)) :=
    hK3b A B hApos hBpos τ hτ0 (Tf.image e) hmem

  have hsum : ∑ ξ ∈ T, ‖(fun v : Fin 2 → AdeleRing (𝓞 ℚ) ℚ =>
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace ℚ (v i).1) * hf (fun i => (v i).2))
      (Matrix.vecMul (rowVec x a b ξ) mM)‖
      = ∑ ξ ∈ T, ‖g (Matrix.vecMul (archRow X A B ξ) (archMat mM))‖
          * ‖hf (Matrix.vecMul (finRow xf ξ) (finMat mM))‖ :=
    Finset.sum_congr rfl fun ξ _ => by rw [tensor_apply_rowVec g hf mM x a b ha hb, norm_mul]
  refine hsum.trans_le ?_
  calc ∑ ξ ∈ T, ‖g (Matrix.vecMul (archRow X A B ξ) (archMat mM))‖
          * ‖hf (Matrix.vecMul (finRow xf ξ) (finMat mM))‖
      = ∑ ξ ∈ Tf, ‖g (Matrix.vecMul (archRow X A B ξ) (archMat mM))‖
          * ‖hf (Matrix.vecMul (finRow xf ξ) (finMat mM))‖ :=
        (Finset.sum_filter_of_ne
          (p := fun ξ => hf (Matrix.vecMul (finRow xf ξ) (finMat mM)) ≠ 0)
          fun ξ _ hne => fun h0 => hne (by rw [h0, norm_zero, mul_zero])).symm
    _ ≤ ∑ ξ ∈ Tf, (D * max H₀ 0) * ker (e ξ) := Finset.sum_le_sum hterm
    _ = (D * max H₀ 0) * ∑ p ∈ Tf.image e, ker p := by
        rw [← Finset.mul_sum, Finset.sum_image fun ξ _ ξ' _ h => he h]
    _ ≤ (D * max H₀ 0) * (C * (1 + (mixedEmbedding.norm A)⁻¹)
          * (1 + (mixedEmbedding.norm B)⁻¹)
          * (min 1 ((mixedEmbedding.norm A)⁻¹ ^ N) + min 1 ((mixedEmbedding.norm B)⁻¹ ^ N))) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = D * max H₀ 0 * C * rhsN N (ideleNorm ℚ a) (ideleNorm ℚ b) := by
        rw [rhsN, ← hNA, ← hNB]
        ring

theorem finBound_zero (K : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (N : ℕ) :
    FinBound (0 : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) K N :=
  ⟨0, le_rfl, fun m _ x a b _ _ T _ => by simp⟩

theorem finBound_add {Φ Ψ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} {K : Set (AdelicGL2 (𝓞 ℚ) ℚ)} {N : ℕ}
    (hΦ : FinBound Φ K N) (hΨ : FinBound Ψ K N) : FinBound (Φ + Ψ) K N := by
  obtain ⟨C₁, hC₁, h₁⟩ := hΦ
  obtain ⟨C₂, hC₂, h₂⟩ := hΨ
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun m hm x a b ha hb T hT => ?_⟩
  calc ∑ ξ ∈ T, ‖(Φ + Ψ) (Matrix.vecMul (rowVec x a b ξ)
          (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖
      ≤ ∑ ξ ∈ T, (‖Φ (Matrix.vecMul (rowVec x a b ξ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖
          + ‖Ψ (Matrix.vecMul (rowVec x a b ξ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖) :=
        Finset.sum_le_sum fun ξ _ => norm_add_le _ _
    _ ≤ C₁ * rhsN N (ideleNorm ℚ a) (ideleNorm ℚ b) + C₂ * rhsN N (ideleNorm ℚ a) (ideleNorm ℚ b) := by
        rw [Finset.sum_add_distrib]
        exact add_le_add (h₁ m hm x a b ha hb T hT) (h₂ m hm x a b ha hb T hT)
    _ = (C₁ + C₂) * rhsN N (ideleNorm ℚ a) (ideleNorm ℚ b) := by ring

theorem finBound_smul (c : ℂ) {Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} {K : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    {N : ℕ} (hΦ : FinBound Φ K N) : FinBound (c • Φ) K N := by
  obtain ⟨C, hC, h⟩ := hΦ
  refine ⟨‖c‖ * C, by positivity, fun m hm x a b ha hb T hT => ?_⟩
  calc ∑ ξ ∈ T, ‖(c • Φ) (Matrix.vecMul (rowVec x a b ξ)
          (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖
      = ‖c‖ * ∑ ξ ∈ T, ‖Φ (Matrix.vecMul (rowVec x a b ξ)
          (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ξ _ => by rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    _ ≤ ‖c‖ * (C * rhsN N (ideleNorm ℚ a) (ideleNorm ℚ b)) :=
        mul_le_mul_of_nonneg_left (h m hm x a b ha hb T hT) (norm_nonneg _)
    _ = ‖c‖ * C * rhsN N (ideleNorm ℚ a) (ideleNorm ℚ b) := by ring

theorem finBound_of_mem {Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 ℚ)
    {K : Set (AdelicGL2 (𝓞 ℚ) ℚ)} (hK : IsCompact K) (N : ℕ) : FinBound Φ K N := by
  refine schwartzBruhat2_induction (p := fun Φ _ => FinBound Φ K N) (fun Φ hΦt => ?_)
    (finBound_zero K N) (fun Φ Ψ _ _ hΦ hΨ => finBound_add hΦ hΨ)
    (fun c Φ _ hΦ => finBound_smul c hΦ) hΦ
  obtain ⟨g, hf, hlc, hcs, rfl⟩ := hΦt
  exact finBound_tensor g hf hlc hcs hK N

theorem summable_and_tsum_le_of_finBound {Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ}
    {K : Set (AdelicGL2 (𝓞 ℚ) ℚ)} {N : ℕ} (hΦ : FinBound Φ K N) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m ∈ K, ∀ (x : AdeleRing (𝓞 ℚ) ℚ) (a b : (AdeleRing (𝓞 ℚ) ℚ)ˣ),
        (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 → (b : AdeleRing (𝓞 ℚ) ℚ).2 = 1 →
        Summable (fun ξ : Fin 2 → ℚ =>
          ‖Φ (Matrix.vecMul (rowVec x a b ξ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖) ∧
        ∑' ξ : {ξ : Fin 2 → ℚ // ξ ≠ 0},
          ‖Φ (Matrix.vecMul (rowVec x a b ξ.1) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖
          ≤ C * (1 + (ideleNorm ℚ a)⁻¹) * (1 + (ideleNorm ℚ b)⁻¹)
              * (min 1 ((ideleNorm ℚ a)⁻¹ ^ N) + min 1 ((ideleNorm ℚ b)⁻¹ ^ N)) := by
  obtain ⟨C, hC0, hC⟩ := hΦ
  refine ⟨C, hC0, fun m hm x a b ha hb => ?_⟩
  set f : (Fin 2 → ℚ) → ℝ := fun ξ =>
    ‖Φ (Matrix.vecMul (rowVec x a b ξ) (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖ with hf
  have hf0 : 0 ≤ f := fun ξ => norm_nonneg _
  have hbound : ∀ T : Finset (Fin 2 → ℚ), (∀ ξ ∈ T, ξ ≠ 0) →
      ∑ ξ ∈ T, f ξ ≤ C * rhsN N (ideleNorm ℚ a) (ideleNorm ℚ b) :=
    fun T hT => hC m hm x a b ha hb T hT
  have hR : C * rhsN N (ideleNorm ℚ a) (ideleNorm ℚ b)
      = C * (1 + (ideleNorm ℚ a)⁻¹) * (1 + (ideleNorm ℚ b)⁻¹)
          * (min 1 ((ideleNorm ℚ a)⁻¹ ^ N) + min 1 ((ideleNorm ℚ b)⁻¹ ^ N)) := by
    unfold rhsN
    ring
  refine ⟨summable_of_sum_le hf0 (c := f 0 + C * rhsN N (ideleNorm ℚ a) (ideleNorm ℚ b))
    fun T => ?_, ?_⟩
  · rw [← Finset.sum_filter_add_sum_filter_not T (fun ξ => ξ = 0)]
    refine add_le_add ?_ (hbound _ fun ξ hξ => (Finset.mem_filter.1 hξ).2)
    calc ∑ ξ ∈ T.filter (fun ξ => ξ = 0), f ξ ≤ ∑ ξ ∈ {0}, f ξ :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun ξ hξ => Finset.mem_singleton.2 (Finset.mem_filter.1 hξ).2) (fun _ _ _ => hf0 _)
      _ = f 0 := Finset.sum_singleton _ _
  · rw [← hR]
    refine Real.tsum_le_of_sum_le (fun ξ => hf0 _) fun S => ?_
    have h := hbound (S.map (Function.Embedding.subtype _)) fun ξ hξ => by
      rw [Finset.mem_map] at hξ
      obtain ⟨ξ', _, rfl⟩ := hξ
      exact ξ'.2
    rw [Finset.sum_map] at h
    exact h

end NumberField.AdelicFourier.ThetaBoundSol

end

open NumberField.AdelicFourier.ThetaBoundSol in
theorem solution
    (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 ℚ)
    (K : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (hK : IsCompact K) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m ∈ K, ∀ (x : AdeleRing (𝓞 ℚ) ℚ) (a b : (AdeleRing (𝓞 ℚ) ℚ)ˣ),
        (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 → (b : AdeleRing (𝓞 ℚ) ℚ).2 = 1 →
        Summable (fun ξ : Fin 2 → ℚ =>
          ‖Φ (Matrix.vecMul
              ![(a : AdeleRing (𝓞 ℚ) ℚ) * algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ 0),
                (b : AdeleRing (𝓞 ℚ) ℚ) *
                  (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ 0) * x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ 1))]
              (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖) ∧
        ∑' ξ : {ξ : Fin 2 → ℚ // ξ ≠ 0},
          ‖Φ (Matrix.vecMul
              ![(a : AdeleRing (𝓞 ℚ) ℚ) * algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ.1 0),
                (b : AdeleRing (𝓞 ℚ) ℚ) *
                  (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ.1 0) * x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ.1 1))]
              (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖
          ≤ C * (1 + (ideleNorm ℚ a)⁻¹) * (1 + (ideleNorm ℚ b)⁻¹)
              * (min 1 ((ideleNorm ℚ a)⁻¹ ^ N) + min 1 ((ideleNorm ℚ b)⁻¹ ^ N)) := by
  obtain ⟨C, hC0, hC⟩ := summable_and_tsum_le_of_finBound (finBound_of_mem hΦ hK N)
  exact ⟨C, hC0, fun m hm x a b ha hb => hC m hm x a b ha hb⟩

end S_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_vecMul_le_mul_one_add_inv_ideleNorm_of_mem_schwartzBruhat2_rat
end P2MW
export P2MW.S_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_vecMul_le_mul_one_add_inv_ideleNorm_of_mem_schwartzBruhat2_rat (solution)
