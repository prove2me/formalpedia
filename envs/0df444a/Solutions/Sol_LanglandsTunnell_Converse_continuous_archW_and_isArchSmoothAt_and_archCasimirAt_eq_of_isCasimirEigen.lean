-- Prove2me | solution 1 for LanglandsTunnell.Converse.continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/76c2e992-5ae8-5615-b5ee-549f62779c2d

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen

set_option autoImplicit false

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

noncomputable section

namespace Ws23
namespace AWL

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchCasimir
open Matrix
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

theorem archComponent_glArch_archRealGLAt_self {w : InfinitePlace K} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archComponent K w (glArch (𝓞 K) K (archRealGLAt hw m)) = glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
  unfold archRealGLAt adelicArchGLInclAt
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_self]

theorem archComponent_glArch_archRealGLAt_of_ne {v w : InfinitePlace K} (hvw : v ≠ w) (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archComponent K v (glArch (𝓞 K) K (archRealGLAt hw m)) = 1 := by
  unfold archRealGLAt adelicArchGLInclAt
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_of_ne K hvw]

theorem realComponent_eq {w : InfinitePlace K} (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) :
    realComponent w hw g = ((archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion).map (ringEquivRealOfIsReal hw) := by
  ext i j
  rfl

theorem complexComponent_eq {w : InfinitePlace K} (hw : w.IsComplex) (g : AdelicGL2 (𝓞 K) K) :
    complexComponent w hw g = ((archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion).map (ringEquivComplexOfIsComplex hw) := by
  ext i j
  rfl

theorem realComponent_mul_of_glArch_eq {w : InfinitePlace K} (hw : w.IsReal) {g g' : AdelicGL2 (𝓞 K) K}
    (h : glArch (𝓞 K) K g = glArch (𝓞 K) K g') : realComponent w hw g = realComponent w hw g' := by
  rw [realComponent_eq, realComponent_eq, h]

theorem complexComponent_mul_of_glArch_eq {w : InfinitePlace K} (hw : w.IsComplex) {g g' : AdelicGL2 (𝓞 K) K}
    (h : glArch (𝓞 K) K g = glArch (𝓞 K) K g') : complexComponent w hw g = complexComponent w hw g' := by
  rw [complexComponent_eq, complexComponent_eq, h]

theorem realComponent_mul_archRealGLAt_self {w : InfinitePlace K} (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K)
    (m : GL (Fin 2) ℝ) :
    realComponent w hw (g * archRealGLAt hw m) = realComponent w hw g * (m : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [realComponent_eq, realComponent_eq, map_mul, map_mul, Units.val_mul, Matrix.map_mul,
    archComponent_glArch_archRealGLAt_self]
  congr 1
  ext i j
  exact (ringEquivRealOfIsReal hw).apply_symm_apply _

theorem realComponent_mul_archRealGLAt_of_ne {v w : InfinitePlace K} (hvw : v ≠ w) (hv : v.IsReal) (hw : w.IsReal)
    (g : AdelicGL2 (𝓞 K) K) (m : GL (Fin 2) ℝ) :
    realComponent v hv (g * archRealGLAt hw m) = realComponent v hv g := by
  rw [realComponent_eq, realComponent_eq, map_mul, map_mul, archComponent_glArch_archRealGLAt_of_ne hvw, mul_one]

theorem complexComponent_mul_archRealGLAt {v w : InfinitePlace K} (hv : v.IsComplex) (hw : w.IsReal)
    (g : AdelicGL2 (𝓞 K) K) (m : GL (Fin 2) ℝ) :
    complexComponent v hv (g * archRealGLAt hw m) = complexComponent v hv g := by
  have hvw : v ≠ w := fun h => (not_isReal_iff_isComplex.mpr hv) (h ▸ hw)
  rw [complexComponent_eq, complexComponent_eq, map_mul, map_mul, archComponent_glArch_archRealGLAt_of_ne hvw, mul_one]

theorem det_realComponent_ne_zero {w : InfinitePlace K} (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) :
    (realComponent w hw g).det ≠ 0 := by
  rw [realComponent_eq]
  have e : ((archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).map
      (ringEquivRealOfIsReal hw) = (ringEquivRealOfIsReal hw).toRingHom.mapMatrix
        ((archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) := rfl
  rw [e, ← RingHom.map_det]
  exact (map_ne_zero_iff (ringEquivRealOfIsReal hw).toRingHom (ringEquivRealOfIsReal hw).injective).mpr
    (Matrix.GeneralLinearGroup.det_ne_zero _)

theorem det_complexComponent_ne_zero {w : InfinitePlace K} (hw : w.IsComplex) (g : AdelicGL2 (𝓞 K) K) :
    (complexComponent w hw g).det ≠ 0 := by
  rw [complexComponent_eq]
  have e : ((archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).map
      (ringEquivComplexOfIsComplex hw) = (ringEquivComplexOfIsComplex hw).toRingHom.mapMatrix
        ((archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) := rfl
  rw [e, ← RingHom.map_det]
  exact (map_ne_zero_iff (ringEquivComplexOfIsComplex hw).toRingHom (ringEquivComplexOfIsComplex hw).injective).mpr
    (Matrix.GeneralLinearGroup.det_ne_zero _)

theorem continuous_ringEquivRealOfIsReal {w : InfinitePlace K} (hw : w.IsReal) : Continuous (ringEquivRealOfIsReal hw) :=
  (AddMonoidHomClass.isometry_of_norm (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)).continuous

theorem continuous_ringEquivComplexOfIsComplex {w : InfinitePlace K} (hw : w.IsComplex) :
    Continuous (ringEquivComplexOfIsComplex hw) :=
  (isometry_extensionEmbedding w).continuous

theorem continuous_realComponent {w : InfinitePlace K} (hw : w.IsReal) : Continuous (realComponent (K := K) w hw) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun g : AdelicGL2 (𝓞 K) K => realComponent w hw g i j
  simp only [realComponent_eq, Matrix.map_apply, archComponent_apply]
  exact (continuous_ringEquivRealOfIsReal hw).comp ((continuous_apply w).comp
    ((continuous_id.matrix_elem i j).comp (Units.continuous_val.comp (continuous_glArch (𝓞 K) K))))

theorem continuous_complexComponent {w : InfinitePlace K} (hw : w.IsComplex) : Continuous (complexComponent (K := K) w hw) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun g : AdelicGL2 (𝓞 K) K => complexComponent w hw g i j
  simp only [complexComponent_eq, Matrix.map_apply, archComponent_apply]
  exact (continuous_ringEquivComplexOfIsComplex hw).comp ((continuous_apply w).comp
    ((continuous_id.matrix_elem i j).comp (Units.continuous_val.comp (continuous_glArch (𝓞 K) K))))

theorem continuous_comp_of_contDiffOn_glSetR {X : Type*} [TopologicalSpace X] {W : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet) {c : X → Matrix (Fin 2) (Fin 2) ℝ} (hc : Continuous c)
    (hdet : ∀ x, (c x).det ≠ 0) : Continuous fun x => W (c x) := by
  have h : ContinuousOn (ArchR.asPi W) ArchR.glSet := hW.continuousOn
  exact h.comp_continuous hc fun x => hdet x

theorem continuous_comp_of_contDiffOn_glSetC {X : Type*} [TopologicalSpace X] {W : Matrix (Fin 2) (Fin 2) ℂ → ℂ}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) (ArchC.asPi W) ArchC.glSet) {c : X → Matrix (Fin 2) (Fin 2) ℂ} (hc : Continuous c)
    (hdet : ∀ x, (c x).det ≠ 0) : Continuous fun x => W (c x) := by
  have h : ContinuousOn (ArchC.asPi W) ArchC.glSet := hW.continuousOn
  exact h.comp_continuous hc fun x => hdet x

section Family

variable (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
  (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
  (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
  (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))

def factor (v : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  if hv : v.IsReal then (dR v hv).W (realComponent v hv g)
  else (dC v (not_isReal_iff_isComplex.mp hv)).W (complexComponent v (not_isReal_iff_isComplex.mp hv) g)

theorem archW_eq_prod (g : AdelicGL2 (𝓞 K) K) : archW archR archC dR dC g = ∏ v, factor archR archC dR dC v g := rfl

theorem continuous_factor (v : InfinitePlace K) : Continuous (factor archR archC dR dC v) := by
  by_cases hv : v.IsReal
  · have e : factor archR archC dR dC v = fun g => (dR v hv).W (realComponent v hv g) := by
      funext g; simp only [factor, dif_pos hv]
    rw [e]
    exact continuous_comp_of_contDiffOn_glSetR (dR v hv).smooth (continuous_realComponent hv) (det_realComponent_ne_zero hv)
  · have e : factor archR archC dR dC v = fun g => (dC v (not_isReal_iff_isComplex.mp hv)).W
        (complexComponent v (not_isReal_iff_isComplex.mp hv) g) := by
      funext g; simp only [factor, dif_neg hv]
    rw [e]
    exact continuous_comp_of_contDiffOn_glSetC (dC v _).smooth (continuous_complexComponent _) (det_complexComponent_ne_zero _)

theorem factor_congr_glArch (v : InfinitePlace K) {g g' : AdelicGL2 (𝓞 K) K} (h : glArch (𝓞 K) K g = glArch (𝓞 K) K g') :
    factor archR archC dR dC v g = factor archR archC dR dC v g' := by
  by_cases hv : v.IsReal
  · simp only [factor, dif_pos hv, realComponent_mul_of_glArch_eq hv h]
  · simp only [factor, dif_neg hv, complexComponent_mul_of_glArch_eq _ h]

theorem factor_mul_archRealGLAt_of_ne {v w : InfinitePlace K} (hvw : v ≠ w) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K)
    (m : GL (Fin 2) ℝ) : factor archR archC dR dC v (g * archRealGLAt hw m) = factor archR archC dR dC v g := by
  by_cases hv : v.IsReal
  · simp only [factor, dif_pos hv, realComponent_mul_archRealGLAt_of_ne hvw hv hw]
  · simp only [factor, dif_neg hv, complexComponent_mul_archRealGLAt _ hw]

def rest (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) : ℂ := ∏ v ∈ Finset.univ.erase w, factor archR archC dR dC v g

theorem rest_mul_archRealGLAt {w : InfinitePlace K} (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) (m : GL (Fin 2) ℝ) :
    rest archR archC dR dC w (g * archRealGLAt hw m) = rest archR archC dR dC w g :=
  Finset.prod_congr rfl fun v hv => factor_mul_archRealGLAt_of_ne archR archC dR dC (Finset.ne_of_mem_erase hv) hw g m

def liftAt (w : InfinitePlace K) (hw : w.IsReal) (Φ : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  Φ (realComponent w hw g) * rest archR archC dR dC w g

theorem archW_eq_liftAt {w : InfinitePlace K} (hw : w.IsReal) :
    archW archR archC dR dC = liftAt archR archC dR dC w hw (dR w hw).W := by
  funext g
  rw [archW_eq_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), liftAt, rest]
  simp only [factor, dif_pos hw]

theorem liftAt_mul_archRealGLAt {w : InfinitePlace K} (hw : w.IsReal) (Φ : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (g : AdelicGL2 (𝓞 K) K) (m : GL (Fin 2) ℝ) :
    liftAt archR archC dR dC w hw Φ (g * archRealGLAt hw m) =
      Φ (realComponent w hw g * (m : Matrix (Fin 2) (Fin 2) ℝ)) * rest archR archC dR dC w g := by
  rw [liftAt, realComponent_mul_archRealGLAt_self, rest_mul_archRealGLAt]

theorem archDerivAt_liftAt {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (Φ : Matrix (Fin 2) (Fin 2) ℝ → ℂ) :
    archDerivAt hw d (liftAt archR archC dR dC w hw Φ) = liftAt archR archC dR dC w hw (matrixFlowDeriv d Φ) := by
  funext g
  show deriv (fun t : ℝ => liftAt archR archC dR dC w hw Φ (g * archFlowAt hw d t)) 0 = _
  have e : (fun t : ℝ => liftAt archR archC dR dC w hw Φ (g * archFlowAt hw d t)) =
      fun t => (fun t => Φ (realComponent w hw g * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) t *
        rest archR archC dR dC w g := by
    funext t
    exact liftAt_mul_archRealGLAt archR archC dR dC hw Φ g _
  rw [e, deriv_mul_const_field]
  rfl

theorem archCasimirAt_liftAt {w : InfinitePlace K} (hw : w.IsReal) (Φ : Matrix (Fin 2) (Fin 2) ℝ → ℂ) :
    archCasimirAt hw (liftAt archR archC dR dC w hw Φ) = liftAt archR archC dR dC w hw (matrixCasimir Φ) := by
  funext g
  simp only [archCasimirAt, archDerivAt_liftAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [liftAt, matrixCasimir, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem isArchSmoothAt_liftAt {w : InfinitePlace K} (hw : w.IsReal) {Φ : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi Φ) ArchR.glSet) : IsArchSmoothAt hw (liftAt archR archC dR dC w hw Φ) := by
  intro g
  set A : Matrix (Fin 2) (Fin 2) ℝ := realComponent w hw g with hA
  have hAdet : A.det ≠ 0 := det_realComponent_ne_zero hw g

  have hcongr : ∀ e ∈ {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0},
      liftAt archR archC dR dC w hw Φ (g * archRealLiftAt hw e) = Φ (A * Matrix.of e) * rest archR archC dR dC w g := by
    intro e he
    rw [archRealLiftAt_of_det_ne_zero hw he, liftAt_mul_archRealGLAt]
    rfl
  refine ContDiffOn.congr ?_ hcongr
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of.symm (A * Matrix.of e) : Fin 2 → Fin 2 → ℝ)) := by
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    simp only [Matrix.of_symm_apply, Matrix.mul_apply]
    exact ContDiff.sum fun l _ => contDiff_const.mul ((contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 2 → ℝ) l))
  have hmaps : Set.MapsTo (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of.symm (A * Matrix.of e) : Fin 2 → Fin 2 → ℝ))
      {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0} ArchR.glSet := by
    intro e he
    show (Matrix.of (Matrix.of.symm (A * Matrix.of e))).det ≠ 0
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero hAdet he
  have hcomp := hΦ.comp hlin.contDiffOn hmaps
  exact hcomp.mul contDiffOn_const

end Family

theorem main (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (w : InfinitePlace K) (hw : w.IsReal)
    (h : ArchCasimir.IsCasimirEigen (dR w hw)) :
    Continuous (archW archR archC dR dC) ∧
    (∀ (g k : AdelicGL2 (𝓞 K) K), glArch (𝓞 K) K k = 1 → archW archR archC dR dC (g * k) = archW archR archC dR dC g) ∧
    IsArchSmoothAt hw (archW archR archC dR dC) ∧
    archCasimirAt hw (archW archR archC dR dC) = (laplaceEigenvalue (archR w hw)) • archW archR archC dR dC := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : archW archR archC dR dC = fun g => ∏ v, factor archR archC dR dC v g := funext fun g => rfl
    rw [e]
    exact continuous_finsetProd _ fun v _ => continuous_factor archR archC dR dC v
  · intro g k hk
    rw [archW_eq_prod, archW_eq_prod]
    exact Finset.prod_congr rfl fun v _ => factor_congr_glArch archR archC dR dC v (by rw [map_mul, hk, mul_one])
  · rw [archW_eq_liftAt archR archC dR dC hw]
    exact isArchSmoothAt_liftAt archR archC dR dC hw (dR w hw).smooth
  · rw [archW_eq_liftAt archR archC dR dC hw, archCasimirAt_liftAt]
    funext g
    simp only [liftAt, Pi.smul_apply, smul_eq_mul]
    rw [h _ (det_realComponent_ne_zero hw g)]
    ring

end Ws23.AWL

end

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

theorem solution
    (K : Type) [Field K] [NumberField K]
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (w : InfinitePlace K) (hw : w.IsReal)
    (h : ArchCasimir.IsCasimirEigen (dR w hw)) :
    Continuous (archW archR archC dR dC) ∧
    (∀ (g k : AdelicGL2 (𝓞 K) K), glArch (𝓞 K) K k = 1 → archW archR archC dR dC (g * k) = archW archR archC dR dC g) ∧
    IsArchSmoothAt hw (archW archR archC dR dC) ∧
    archCasimirAt hw (archW archR archC dR dC) = (laplaceEigenvalue (archR w hw)) • archW archR archC dR dC :=
  Ws23.AWL.main archR archC dR dC w hw h

end S_LanglandsTunnell_Converse_continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen
end P2MW
export P2MW.S_LanglandsTunnell_Converse_continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen (solution)
