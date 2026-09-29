-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog.spaceGroupCatalog_affine_cover
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T11:06:29.473128+00:00
-- url     : https://prove2.me/submissions/aca3dd48-e72f-4a90-88f6-4c513123c6f9

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog

/-!
Each catalogue group is affinely equivalent to its affine-class representative: either it is
the representative itself, or it is its mirror image under the point inversion `x ↦ -x`.
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

/-- the point inversion `x ↦ -x` -/
noncomputable def inversion : EuclideanIsom 3 :=
  (LinearIsometryEquiv.neg ℝ).toAffineIsometryEquiv

lemma inversion_apply (x : E 3) : inversion x = -x := rfl

lemma inversion_inv_apply (x : E 3) : inversion⁻¹ x = -x := rfl

lemma SymOp.mirror_compatible {k : LatticeKind} {o : SymOp} (h : o.Compatible k) :
    o.mirror.Compatible k := h

lemma SymOp.mirror_mirror (o : SymOp) : o.mirror.mirror = o := by
  cases o
  simp [SymOp.mirror]

lemma toIsom_mirror {k : LatticeKind} {o : SymOp} (h : o.Compatible k) :
    o.mirror.toIsom k = inversion * o.toIsom k * inversion⁻¹ := by
  ext1 x
  obtain ⟨u, rfl⟩ := coordMap_surjective k x
  rw [toIsom_coordMap (SymOp.mirror_compatible h), AffineIsometryEquiv.coe_mul,
    AffineIsometryEquiv.coe_mul, Function.comp_apply, Function.comp_apply, inversion_inv_apply,
    ← map_neg, toIsom_coordMap h, inversion_apply, ← map_neg]
  congr 1
  funext i
  simp [SymOp.coordAction, SymOp.mirror, Matrix.mulVec_neg]
  ring

lemma latticeOps_mirror : ∀ o ∈ latticeOps, o.mirror ∈ latticeOps := by
  intro o ho
  simp only [latticeOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [latticeOps, SymOp.mirror]

lemma mirror_genset (D : SpaceGroupData)
    (hD : ∀ o ∈ latticeOps ++ D.gens, o.Compatible D.kind) :
    {g | ∃ o ∈ latticeOps ++ D.mirror.gens, g = o.toIsom D.mirror.kind} =
      (MulAut.conj inversion) '' {g | ∃ o ∈ latticeOps ++ D.gens, g = o.toIsom D.kind} := by
  ext g
  constructor
  · rintro ⟨o, ho, rfl⟩
    have ho' : o.mirror ∈ latticeOps ++ D.gens := by
      rcases List.mem_append.1 ho with h | h
      · exact List.mem_append_left _ (latticeOps_mirror o h)
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.1 h
        rw [SymOp.mirror_mirror]
        exact List.mem_append_right _ ho'
    refine ⟨o.mirror.toIsom D.kind, ⟨o.mirror, ho', rfl⟩, ?_⟩
    rw [MulAut.conj_apply, ← toIsom_mirror (hD _ ho'), SymOp.mirror_mirror]
    rfl
  · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
    have ho' : o.mirror ∈ latticeOps ++ D.mirror.gens := by
      rcases List.mem_append.1 ho with h | h
      · exact List.mem_append_left _ (latticeOps_mirror o h)
      · exact List.mem_append_right _ (List.mem_map_of_mem h)
    refine ⟨o.mirror, ho', ?_⟩
    rw [MulAut.conj_apply, ← toIsom_mirror (hD _ ho)]
    rfl

lemma mirror_toSubgroup (D : SpaceGroupData)
    (hD : ∀ o ∈ latticeOps ++ D.gens, o.Compatible D.kind) :
    D.mirror.toSubgroup = D.toSubgroup.map (MulAut.conj inversion).toMonoidHom := by
  rw [SpaceGroupData.toSubgroup, SpaceGroupData.toSubgroup, MonoidHom.map_closure,
    mirror_genset D hD]
  rfl

lemma affinelyEquivalent_refl (G : Subgroup (EuclideanIsom 3)) : AffinelyEquivalent G G :=
  ⟨1, by simp⟩

lemma affinelyEquivalent_conj (G : Subgroup (EuclideanIsom 3)) (c : EuclideanIsom 3) :
    AffinelyEquivalent G (G.map (MulAut.conj c).toMonoidHom) := by
  refine ⟨c.toAffineEquiv, ?_⟩
  have key : ∀ g : EuclideanIsom 3, (c * g * c⁻¹).toAffineEquiv =
      c.toAffineEquiv * g.toAffineEquiv * c.toAffineEquiv⁻¹ := by
    intro g
    ext x
    rfl
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨c * g * c⁻¹, ⟨g, hg, rfl⟩, (key g).symm⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, key g⟩


set_option maxRecDepth 100000 in
theorem catalogData_enantio :
    ∀ i : Fin 230, catalogData (affineRepIndex (affineClassIndex i)) = catalogData i ∨
      (catalogData (affineRepIndex (affineClassIndex i))).mirror = catalogData i := by
  decide +kernel

theorem catalog_affine_cover :
    ∀ i : Fin 230,
      AffinelyEquivalent (spaceGroupCatalog (affineRepIndex (affineClassIndex i)))
        (spaceGroupCatalog i) := by
  intro i
  rcases catalogData_enantio i with h | h
  · rw [spaceGroupCatalog, spaceGroupCatalog, h]
    exact affinelyEquivalent_refl _
  · rw [spaceGroupCatalog, spaceGroupCatalog, ← h,
      mirror_toSubgroup _ (catalogData_compatible _)]
    exact affinelyEquivalent_conj _ _

end LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog

open LeanEval.Geometry.SpaceGroupsProblem LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog in
theorem solution :
    ∀ i : Fin 230,
      AffinelyEquivalent (spaceGroupCatalog (affineRepIndex (affineClassIndex i)))
        (spaceGroupCatalog i) :=
  catalog_affine_cover
