-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog.spaceGroupCatalog_sohncke
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T11:06:29.122472+00:00
-- url     : https://prove2.me/submissions/26c8949e-4d92-4fbf-9341-6105cef6b73d

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog

/-!
Sohncke bookkeeping for the catalogue: a catalogue group consists of orientation-preserving
isometries iff all its generators have positive determinant, which is decided for all 230
entries.
-/

namespace LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog
open Matrix

/-- quadratic form `u ⬝ (Q u)` with `Q` twice the Gram matrix -/
noncomputable def qf (k : LatticeKind) (u : Fin 3 → ℝ) : ℝ :=
  u ⬝ᵥ ((k.gram2.map (Int.cast : ℤ → ℝ)) *ᵥ u)

lemma qf_cubic (u : Fin 3 → ℝ) : qf .cubic u = 2 * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) := by
  simp [qf, LatticeKind.gram2, dotProduct, mulVec, Fin.sum_univ_three]; ring

lemma qf_hex (u : Fin 3 → ℝ) :
    qf .hex u = 2 * (u 0 ^ 2 - u 0 * u 1 + u 1 ^ 2 + u 2 ^ 2) := by
  simp [qf, LatticeKind.gram2, dotProduct, mulVec, Fin.sum_univ_three]; ring

lemma coordMap_ofLp (k : LatticeKind) (u : Fin 3 → ℝ) :
    (k.coordMap u).ofLp = k.basisMatrix *ᵥ u := by
  simp [LatticeKind.coordMap, Matrix.toLin'_apply]

lemma norm_coordMap_sq (k : LatticeKind) (u : Fin 3 → ℝ) :
    ‖k.coordMap u‖ ^ 2 = qf k u / 2 := by
  rw [EuclideanSpace.norm_sq_eq, coordMap_ofLp]
  cases k
  · simp [qf_cubic, LatticeKind.basisMatrix, Fin.sum_univ_three]
  · have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    simp [qf_hex, LatticeKind.basisMatrix, Fin.sum_univ_three, mulVec, dotProduct]
    ring_nf; rw [h3]; ring


lemma qf_pos_def (k : LatticeKind) (u : Fin 3 → ℝ) (h : qf k u = 0) : u = 0 := by
  have h0 : u 0 = 0 ∧ u 1 = 0 ∧ u 2 = 0 := by
    cases k
    · rw [qf_cubic] at h
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
    · rw [qf_hex] at h
      refine ⟨?_, ?_, ?_⟩ <;>
        nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 0 - u 1),
          sq_nonneg (2 * u 0 - u 1), sq_nonneg (u 0 - 2 * u 1)]
  funext i; fin_cases i <;> simp [h0.1, h0.2.1, h0.2.2]

lemma coordMap_injective (k : LatticeKind) : Function.Injective k.coordMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  apply qf_pos_def k
  have := norm_coordMap_sq k u
  rw [hu, norm_zero] at this
  linarith

noncomputable def coordEquiv (k : LatticeKind) : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3 :=
  LinearMap.linearEquivOfInjective k.coordMap (coordMap_injective k) (by simp)

@[simp] lemma coordEquiv_apply (k : LatticeKind) (u : Fin 3 → ℝ) :
    coordEquiv k u = k.coordMap u := rfl

lemma coordMap_surjective (k : LatticeKind) : Function.Surjective k.coordMap :=
  (coordEquiv k).surjective

/-- compatibility of an operation with the lattice metric -/
def SymOp.Compatible (k : LatticeKind) (o : SymOp) : Prop :=
  o.rot.transpose * k.gram2 * o.rot = k.gram2

instance (k : LatticeKind) (o : SymOp) : Decidable (o.Compatible k) :=
  inferInstanceAs (Decidable (_ = _))

lemma qf_rot {k : LatticeKind} {o : SymOp} (h : o.Compatible k) (u : Fin 3 → ℝ) :
    qf k (o.rot.map (Int.cast : ℤ → ℝ) *ᵥ u) = qf k u := by
  have hc : (o.rot.map (Int.cast : ℤ → ℝ))ᵀ * k.gram2.map (Int.cast : ℤ → ℝ) *
      o.rot.map (Int.cast : ℤ → ℝ) = k.gram2.map (Int.cast : ℤ → ℝ) := by
    have := congrArg (fun M => (Int.castRingHom ℝ).mapMatrix M) h
    simp only [map_mul, RingHom.mapMatrix_apply] at this
    rw [← Matrix.transpose_map]
    exact this
  unfold qf
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hc]


lemma coordEquiv_symm_coordMap (k : LatticeKind) (u : Fin 3 → ℝ) :
    (coordEquiv k).symm (k.coordMap u) = u := by
  rw [← coordEquiv_apply, LinearEquiv.symm_apply_apply]

/-- linear part of an operation, transported to `E 3` -/
noncomputable def linPart (k : LatticeKind) (o : SymOp) : E 3 →ₗ[ℝ] E 3 :=
  (coordEquiv k).toLinearMap ∘ₗ Matrix.toLin' (o.rot.map (Int.cast : ℤ → ℝ)) ∘ₗ
    (coordEquiv k).symm.toLinearMap

lemma linPart_coordMap (k : LatticeKind) (o : SymOp) (u : Fin 3 → ℝ) :
    linPart k o (k.coordMap u) = k.coordMap (o.rot.map (Int.cast : ℤ → ℝ) *ᵥ u) := by
  simp [linPart, coordEquiv_symm_coordMap, Matrix.toLin'_apply]

lemma norm_linPart {k : LatticeKind} {o : SymOp} (h : o.Compatible k) (x : E 3) :
    ‖linPart k o x‖ = ‖x‖ := by
  obtain ⟨u, rfl⟩ := coordMap_surjective k x
  rw [linPart_coordMap]
  have h1 := norm_coordMap_sq k (o.rot.map (Int.cast : ℤ → ℝ) *ᵥ u)
  have h2 := norm_coordMap_sq k u
  rw [qf_rot h] at h1
  rw [← h2] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

/-- translation part in `E 3` -/
noncomputable def transPart (k : LatticeKind) (o : SymOp) : E 3 :=
  k.coordMap (fun i => (o.tr i : ℝ) / 12)

/-- the isometry of a compatible operation -/
noncomputable def isomOf {k : LatticeKind} {o : SymOp} (h : o.Compatible k) : EuclideanIsom 3 :=
  let L : E 3 →ₗᵢ[ℝ] E 3 := { linPart k o with norm_map' := norm_linPart h }
  (L.toLinearIsometryEquiv rfl).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ (E 3) (transPart k o))

lemma isomOf_apply {k : LatticeKind} {o : SymOp} (h : o.Compatible k) (x : E 3) :
    isomOf h x = transPart k o + linPart k o x := rfl

lemma isomOf_coordMap {k : LatticeKind} {o : SymOp} (h : o.Compatible k) (u : Fin 3 → ℝ) :
    isomOf h (k.coordMap u) = k.coordMap (o.coordAction u) := by
  rw [isomOf_apply, linPart_coordMap, transPart, SymOp.coordAction, map_add, add_comm]

lemma toIsom_coordMap {k : LatticeKind} {o : SymOp} (h : o.Compatible k) (u : Fin 3 → ℝ) :
    o.toIsom k (k.coordMap u) = k.coordMap (o.coordAction u) := by
  have hex : ∃ g : EuclideanIsom 3, ∀ u : Fin 3 → ℝ,
      g (k.coordMap u) = k.coordMap (o.coordAction u) := ⟨isomOf h, isomOf_coordMap h⟩
  rw [SymOp.toIsom, dif_pos hex]
  exact hex.choose_spec u

lemma toIsom_eq_isomOf {k : LatticeKind} {o : SymOp} (h : o.Compatible k) :
    o.toIsom k = isomOf h := by
  ext1 x
  obtain ⟨u, rfl⟩ := coordMap_surjective k x
  rw [toIsom_coordMap h, isomOf_coordMap h]


set_option maxRecDepth 100000 in
theorem catalogData_compatible :
    ∀ i : Fin 230, ∀ o ∈ latticeOps ++ (catalogData i).gens, o.Compatible (catalogData i).kind := by
  decide +kernel

/-- the determinant of the linear part, as a homomorphism -/
noncomputable def detHom : EuclideanIsom 3 →* ℝˣ where
  toFun g := LinearEquiv.det g.toAffineEquiv.linear
  map_one' := by
    show LinearEquiv.det (LinearEquiv.refl ℝ (E 3)) = 1
    simp
  map_mul' g h := by
    show LinearEquiv.det (g.toAffineEquiv.linear * h.toAffineEquiv.linear) = _
    rw [map_mul]

lemma isOP_iff (g : EuclideanIsom 3) :
    IsOrientationPreservingIsom g ↔ detHom g ∈ Units.posSubgroup ℝ := by
  rw [Units.mem_posSubgroup]
  rfl

lemma det_toIsom {k : LatticeKind} {o : SymOp} (h : o.Compatible k) :
    ((o.toIsom k).toAffineEquiv.linear.det : ℝ) = (o.rot.det : ℝ) := by
  rw [toIsom_eq_isomOf h, LinearEquiv.coe_det]
  have : ((isomOf h).toAffineEquiv.linear : E 3 →ₗ[ℝ] E 3) = linPart k o := by
    ext x
    rfl
  rw [this, linPart, LinearMap.det_conj, LinearMap.det_toLin']
  rw [show o.rot.map (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ).mapMatrix o.rot from rfl,
    ← RingHom.map_det]
  rfl

theorem SpaceGroupData.sohncke_iff (D : SpaceGroupData)
    (hD : ∀ o ∈ latticeOps ++ D.gens, o.Compatible D.kind) :
    (∀ g, g ∈ D.toSubgroup → IsOrientationPreservingIsom g) ↔
      ∀ o ∈ latticeOps ++ D.gens, 0 < o.rot.det := by
  constructor
  · intro H o ho
    have := H _ (Subgroup.subset_closure ⟨o, ho, rfl⟩)
    rw [IsOrientationPreservingIsom, det_toIsom (hD o ho)] at this
    exact_mod_cast this
  · intro H
    have hle : D.toSubgroup ≤ (Units.posSubgroup ℝ).comap detHom := by
      rw [SpaceGroupData.toSubgroup, Subgroup.closure_le]
      rintro g ⟨o, ho, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, ← isOP_iff, IsOrientationPreservingIsom,
        det_toIsom (hD o ho)]
      exact_mod_cast H o ho
    intro g hg
    rw [isOP_iff]
    exact hle hg


set_option maxRecDepth 100000 in
theorem catalogData_sohncke_iff :
    ∀ i : Fin 230, (∀ o ∈ latticeOps ++ (catalogData i).gens, 0 < o.rot.det) ↔
      ∃ k : Fin 65, sohnckeIndex k = i := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sohnckeIndex_injective : Function.Injective sohnckeIndex := by
  decide +kernel

theorem catalog_sohncke :
    Function.Injective sohnckeIndex ∧
      ∀ i : Fin 230, (∀ g, g ∈ spaceGroupCatalog i → IsOrientationPreservingIsom g) ↔
        ∃ k : Fin 65, sohnckeIndex k = i := by
  refine ⟨sohnckeIndex_injective, fun i => ?_⟩
  rw [spaceGroupCatalog, (catalogData i).sohncke_iff (catalogData_compatible i)]
  exact catalogData_sohncke_iff i

end LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog

open LeanEval.Geometry.SpaceGroupsProblem LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog in
theorem solution :
    Function.Injective sohnckeIndex ∧
      ∀ i : Fin 230, (∀ g, g ∈ spaceGroupCatalog i → IsOrientationPreservingIsom g) ↔
        ∃ k : Fin 65, sohnckeIndex k = i :=
  catalog_sohncke
