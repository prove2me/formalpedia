-- Prove2me | solution 1 for NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/48b1b45f-ab0b-5eab-bf86-9d4b608cf456

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ENNReal

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

set_option linter.unusedSectionVars false

namespace ArchIwasawa

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.InfinitePlace

variable (K : Type) [Field K] [NumberField K]

theorem matrix_eq_of_arch_fin_eq {M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)}
    (h₁ : (adeleArch (𝓞 K) K).mapMatrix M = (adeleArch (𝓞 K) K).mapMatrix N)
    (h₂ : (adeleFin (𝓞 K) K).mapMatrix M = (adeleFin (𝓞 K) K).mapMatrix N) : M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply, adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

def pairMat (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) (b : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  Matrix.of fun i j => ((a i j, b i j) : AdeleRing (𝓞 K) K)

theorem mapMatrix_arch_pairMat (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
    (b : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (adeleArch (𝓞 K) K).mapMatrix (pairMat K a b) = a := by
  ext i j; rfl

theorem mapMatrix_fin_pairMat (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
    (b : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (adeleFin (𝓞 K) K).mapMatrix (pairMat K a b) = b := by
  ext i j; rfl

theorem pairMat_one : pairMat K 1 1 = 1 :=
  matrix_eq_of_arch_fin_eq K (by rw [mapMatrix_arch_pairMat, map_one])
    (by rw [mapMatrix_fin_pairMat, map_one])

theorem pairMat_mul (a a' : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
    (b b' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    pairMat K (a * a') (b * b') = pairMat K a b * pairMat K a' b' :=
  matrix_eq_of_arch_fin_eq K
    (by rw [map_mul, mapMatrix_arch_pairMat, mapMatrix_arch_pairMat, mapMatrix_arch_pairMat])
    (by rw [map_mul, mapMatrix_fin_pairMat, mapMatrix_fin_pairMat, mapMatrix_fin_pairMat])

noncomputable def liftArch (g : GL (Fin 2) (InfiniteAdeleRing K)) : AdelicGL2 (𝓞 K) K where
  val := pairMat K (g : Matrix (Fin 2) (Fin 2) _) 1
  inv := pairMat K ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) _) 1
  val_inv := by rw [← pairMat_mul, Units.mul_inv, mul_one]; exact pairMat_one K
  inv_val := by rw [← pairMat_mul, Units.inv_mul, mul_one]; exact pairMat_one K

theorem glArch_liftArch (g : GL (Fin 2) (InfiniteAdeleRing K)) : glArch (𝓞 K) K (liftArch K g) = g :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

theorem part1 (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    ∃ b ∈ AutomorphicForm.borelSubgroup (InfiniteAdeleRing K),
      ∃ k ∈ (⨅ w : InfinitePlace K,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing K))),
        g = b * k := by
  obtain ⟨b, k, hb, -, hk, hg⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq K (liftArch K g)
  refine ⟨glArch (𝓞 K) K b, ?_, glArch (𝓞 K) K k, ?_, ?_⟩
  · show ((glArch (𝓞 K) K b : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0
    rw [glArch_apply]
    have : ((b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := hb
    rw [this]; rfl
  · rw [Subgroup.mem_iInf]
    intro w
    rw [Subgroup.mem_comap, mem_rowIsometrySubgroup_iff]
    exact hk w
  · rw [← map_mul, ← hg, glArch_liftArch]

theorem continuous_star_matrix (R : Type*) [CommRing R] [StarRing R] [TopologicalSpace R] [ContinuousStar R] :
    Continuous fun A : Matrix (Fin 2) (Fin 2) R => star A := by
  show Continuous fun A : Matrix (Fin 2) (Fin 2) R => A.transpose.map star
  exact (continuous_id.matrix_transpose).matrix_map continuous_star

theorem isCompact_orthogonalGroup :
    IsCompact ((Matrix.orthogonalGroup (Fin 2) ℝ : Submonoid (Matrix (Fin 2) (Fin 2) ℝ)) :
      Set (Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hclosed : IsClosed ((Matrix.orthogonalGroup (Fin 2) ℝ : Submonoid (Matrix (Fin 2) (Fin 2) ℝ)) :
      Set (Matrix (Fin 2) (Fin 2) ℝ)) := by
    rw [show ((Matrix.orthogonalGroup (Fin 2) ℝ : Submonoid (Matrix (Fin 2) (Fin 2) ℝ)) : Set (Matrix (Fin 2) (Fin 2) ℝ)) =
        {A | star A * A = 1} ∩ {A | A * star A = 1} from by ext A; exact Unitary.mem_iff]
    have hc := continuous_star_matrix ℝ
    exact (isClosed_eq (hc.mul continuous_id) continuous_const).inter (isClosed_eq (continuous_id.mul hc) continuous_const)
  have hK : IsCompact (Matrix.of '' Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-1 : ℝ) 1)) :
      Set (Matrix (Fin 2) (Fin 2) ℝ)) :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).image (by exact continuous_id)
  have hsub : ((Matrix.orthogonalGroup (Fin 2) ℝ : Submonoid (Matrix (Fin 2) (Fin 2) ℝ)) : Set (Matrix (Fin 2) (Fin 2) ℝ)) ⊆
      Matrix.of '' Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-1 : ℝ) 1)) := by
    intro A hA
    have h := (Unitary.mem_iff.1 hA).1
    refine ⟨Matrix.of.symm A, ?_, Matrix.of.apply_symm_apply A⟩
    rw [Set.mem_univ_pi]; intro i; rw [Set.mem_univ_pi]; intro j
    rw [Set.mem_Icc, Matrix.of_symm_apply]
    have hjj := congrFun (congrFun h j) j
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at hjj
    simp only [Matrix.star_apply, star_trivial] at hjj
    have hsq : ∀ i : Fin 2, A i j * A i j ≤ 1 := by
      intro i; fin_cases i
      · show A 0 j * A 0 j ≤ 1; nlinarith [mul_self_nonneg (A 0 j), mul_self_nonneg (A 1 j)]
      · show A 1 j * A 1 j ≤ 1; nlinarith [mul_self_nonneg (A 0 j), mul_self_nonneg (A 1 j)]
    exact abs_le.mp (abs_le_one_iff_mul_self_le_one.mpr (hsq i))
  exact hK.of_isClosed_subset hclosed hsub

theorem isCompact_unitaryGroup :
    IsCompact ((Matrix.unitaryGroup (Fin 2) ℂ : Submonoid (Matrix (Fin 2) (Fin 2) ℂ)) :
      Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hclosed : IsClosed ((Matrix.unitaryGroup (Fin 2) ℂ : Submonoid (Matrix (Fin 2) (Fin 2) ℂ)) :
      Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [show ((Matrix.unitaryGroup (Fin 2) ℂ : Submonoid (Matrix (Fin 2) (Fin 2) ℂ)) : Set (Matrix (Fin 2) (Fin 2) ℂ)) =
        {A | star A * A = 1} ∩ {A | A * star A = 1} from by ext A; exact Unitary.mem_iff]
    have hc := continuous_star_matrix ℂ
    exact (isClosed_eq (hc.mul continuous_id) continuous_const).inter (isClosed_eq (continuous_id.mul hc) continuous_const)
  have hK : IsCompact (Matrix.of '' Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ (fun _ : Fin 2 => Metric.closedBall (0 : ℂ) 1)) :
      Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1).image (by exact continuous_id)
  have hsub : ((Matrix.unitaryGroup (Fin 2) ℂ : Submonoid (Matrix (Fin 2) (Fin 2) ℂ)) : Set (Matrix (Fin 2) (Fin 2) ℂ)) ⊆
      Matrix.of '' Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ (fun _ : Fin 2 => Metric.closedBall (0 : ℂ) 1)) := by
    intro A hA
    have h := (Unitary.mem_iff.1 hA).1
    refine ⟨Matrix.of.symm A, ?_, Matrix.of.apply_symm_apply A⟩
    rw [Set.mem_univ_pi]; intro i; rw [Set.mem_univ_pi]; intro j
    rw [Metric.mem_closedBall, dist_zero_right, Matrix.of_symm_apply]
    have hjj := congrFun (congrFun h j) j
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at hjj
    simp only [Matrix.star_apply] at hjj
    have hns : ∀ k : Fin 2, star (A k j) * A k j = ((‖A k j‖ ^ 2 : ℝ) : ℂ) := fun k => by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
    rw [hns, hns, ← Complex.ofReal_add, ← Complex.ofReal_one, Complex.ofReal_inj] at hjj
    have key : ∀ i : Fin 2, ‖A i j‖ ^ 2 ≤ 1 := by
      intro i; fin_cases i
      · show ‖A 0 j‖ ^ 2 ≤ 1; nlinarith [sq_nonneg ‖A 0 j‖, sq_nonneg ‖A 1 j‖]
      · show ‖A 1 j‖ ^ 2 ≤ 1; nlinarith [sq_nonneg ‖A 0 j‖, sq_nonneg ‖A 1 j‖]
    nlinarith [norm_nonneg (A i j), key i]
  exact hK.of_isClosed_subset hclosed hsub

theorem isCompact_rowIsometrySubgroup (w : InfinitePlace K) :
    IsCompact ((rowIsometrySubgroup w.Completion : Subgroup (GL (Fin 2) w.Completion)) : Set (GL (Fin 2) w.Completion)) := by
  rw [isCompact_iff_compactSpace]
  rcases w.isReal_or_isComplex with hw | hw
  · obtain ⟨e, -⟩ := AutomorphicForm.exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal K w hw
    haveI : CompactSpace (Matrix.orthogonalGroup (Fin 2) ℝ) := isCompact_iff_compactSpace.1 isCompact_orthogonalGroup
    exact e.toHomeomorph.symm.compactSpace
  · obtain ⟨e, -⟩ := AutomorphicForm.exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex K w hw
    haveI : CompactSpace (Matrix.unitaryGroup (Fin 2) ℂ) := isCompact_iff_compactSpace.1 isCompact_unitaryGroup
    exact e.toHomeomorph.symm.compactSpace

noncomputable def glue (k : (w : InfinitePlace K) → GL (Fin 2) w.Completion) : GL (Fin 2) (InfiniteAdeleRing K) where
  val := Matrix.of fun i j => fun w => ((k w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
  inv := Matrix.of fun i j => fun w => (((k w)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
  val_inv := by
    ext i j
    funext w
    have h : (((k w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) * (((k w)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)) i j = (1 : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
      rw [Units.mul_inv]
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change ((k w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i 0 * (((k w)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 j + ((k w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i 1 * (((k w)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 j = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j w
    rw [h]
    by_cases hij : i = j
    · subst hij; simp only [Matrix.one_apply_eq]; rfl
    · simp only [Matrix.one_apply_ne hij]; rfl
  inv_val := by
    ext i j
    funext w
    have h : ((((k w)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) * ((k w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)) i j = (1 : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
      rw [Units.inv_mul]
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (((k w)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i 0 * ((k w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 j + (((k w)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i 1 * ((k w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 j = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j w
    rw [h]
    by_cases hij : i = j
    · subst hij; simp only [Matrix.one_apply_eq]; rfl
    · simp only [Matrix.one_apply_ne hij]; rfl

theorem archComponent_glue (k : (w : InfinitePlace K) → GL (Fin 2) w.Completion) (w : InfinitePlace K) :
    archComponent K w (glue K k) = k w :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

theorem glue_archComponent (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    glue K (fun w => archComponent K w g) = g :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

theorem continuous_glue : Continuous (glue K) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => continuous_pi fun w => ?_
    exact ((Units.continuous_val.matrix_elem i j).comp (continuous_apply w))
  · refine continuous_matrix fun i j => continuous_pi fun w => ?_
    exact ((Units.continuous_coe_inv.matrix_elem i j).comp (continuous_apply w))

theorem part2 :
    IsCompact ((⨅ w : InfinitePlace K,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing K))) : Set (GL (Fin 2) (InfiniteAdeleRing K))) := by
  have hset : ((⨅ w : InfinitePlace K,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing K))) : Set (GL (Fin 2) (InfiniteAdeleRing K))) =
      glue K '' Set.pi Set.univ (fun w => (rowIsometrySubgroup w.Completion : Set (GL (Fin 2) w.Completion))) := by
    ext g
    rw [SetLike.mem_coe, Subgroup.mem_iInf]
    constructor
    · intro hg
      refine ⟨fun w => archComponent K w g, ?_, glue_archComponent K g⟩
      simp only [Set.mem_pi, Set.mem_univ, true_implies, SetLike.mem_coe]
      exact fun w => (Subgroup.mem_comap.1 (hg w))
    · rintro ⟨k, hk, rfl⟩ w
      rw [Subgroup.mem_comap, archComponent_glue]
      exact hk w (Set.mem_univ w)
  rw [hset]
  exact (isCompact_univ_pi fun w => isCompact_rowIsometrySubgroup K w).image (continuous_glue K)

end ArchIwasawa

theorem solution
    (K : Type) [Field K] [NumberField K] :
    (∀ g : GL (Fin 2) (InfiniteAdeleRing K),
      ∃ b ∈ AutomorphicForm.borelSubgroup (InfiniteAdeleRing K),
        ∃ k ∈ (⨅ w : InfinitePlace K,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing K))),
          g = b * k) ∧
    IsCompact ((⨅ w : InfinitePlace K,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing K))) : Set (GL (Fin 2) (InfiniteAdeleRing K))) :=
  ⟨ArchIwasawa.part1 K, ArchIwasawa.part2 K⟩

end S_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
end P2MW
export P2MW.S_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup (solution)
