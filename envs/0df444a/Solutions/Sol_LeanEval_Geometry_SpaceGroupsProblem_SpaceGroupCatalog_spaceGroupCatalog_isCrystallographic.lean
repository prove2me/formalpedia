-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog.spaceGroupCatalog_isCrystallographic
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T11:06:28.658669+00:00
-- url     : https://prove2.me/submissions/d8bfa67e-6642-4538-836f-973d3fe4e48a

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog

/-!
Every group of the explicit catalogue `spaceGroupCatalog` is crystallographic: it is
contained in the (discrete) stabiliser of the lattice `(1/12)Λ`, and it contains the three
lattice translations.
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

/-- the lattice `(1/12) Λ` of points with coordinates in `ℤ/12` -/
def lat (k : LatticeKind) : Set (E 3) :=
  {x | ∃ n : Fin 3 → ℤ, x = k.coordMap (fun i => (n i : ℝ) / 12)}

/-- the stabiliser of `lat k` -/
def latStab (k : LatticeKind) : Subgroup (EuclideanIsom 3) where
  carrier := {g | ∀ x, x ∈ lat k ↔ g x ∈ lat k}
  mul_mem' := by
    intro a b ha hb x
    rw [hb x, ha (b x)]
    rfl
  one_mem' := by
    intro x
    rfl
  inv_mem' := by
    intro a ha x
    rw [ha (a⁻¹ x)]
    simp

lemma cast_mulVec_div (R : Matrix (Fin 3) (Fin 3) ℤ) (n : Fin 3 → ℤ) :
    R.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (n i : ℝ) / 12) = fun i => ((R *ᵥ n) i : ℝ) / 12 := by
  funext i
  simp [mulVec, dotProduct, Fin.sum_univ_three]
  ring

lemma det_sq_eq_one {k : LatticeKind} {o : SymOp} (h : o.Compatible k) : o.rot.det ^ 2 = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have hk : k.gram2.det ≠ 0 := by cases k <;> decide
  have : (o.rot.det ^ 2 - 1) * k.gram2.det = 0 := by rw [sq]; linear_combination h1
  rcases mul_eq_zero.1 this with h2 | h2
  · linarith
  · exact absurd h2 hk

lemma toIsom_mem_latStab {k : LatticeKind} {o : SymOp} (h : o.Compatible k) :
    o.toIsom k ∈ latStab k := by
  intro x
  obtain ⟨y, rfl⟩ := coordMap_surjective k x
  rw [toIsom_coordMap h]
  have hu : IsUnit o.rot.det :=
    isUnit_iff_exists_inv.2 ⟨o.rot.det, by rw [← sq]; exact det_sq_eq_one h⟩
  set R' := o.rot⁻¹ with hR'
  have hRR : R'.map (Int.cast : ℤ → ℝ) * o.rot.map (Int.cast : ℤ → ℝ) = 1 := by
    have := congrArg (fun M => (Int.castRingHom ℝ).mapMatrix M) (Matrix.nonsing_inv_mul o.rot hu)
    simp only [map_mul, map_one, RingHom.mapMatrix_apply] at this
    exact this
  constructor
  · rintro ⟨n, hn⟩
    have hy := coordMap_injective k hn
    subst hy
    refine ⟨o.rot *ᵥ n + o.tr, ?_⟩
    congr 1
    rw [SymOp.coordAction, cast_mulVec_div]
    funext i
    simp only [Pi.add_apply, Int.cast_add]
    ring
  · rintro ⟨m, hm⟩
    have hy := coordMap_injective k hm
    refine ⟨R' *ᵥ (m - o.tr), ?_⟩
    congr 1
    rw [← cast_mulVec_div, ← one_mulVec y, ← hRR, ← mulVec_mulVec]
    congr 1
    rw [SymOp.coordAction] at hy
    funext i
    have := congrFun hy i
    simp only [Pi.add_apply] at this
    simp only [Pi.sub_apply, Int.cast_sub]
    linarith


lemma lat_inter_closedBall_finite (k : LatticeKind) (c : E 3) (r : ℝ) :
    (lat k ∩ Metric.closedBall c r).Finite := by
  set T : E 3 →L[ℝ] (Fin 3 → ℝ) :=
    LinearMap.toContinuousLinearMap (coordEquiv k).symm.toLinearMap with hT
  set C : ℝ := 12 * (‖T‖ * (‖c‖ + r)) with hC
  set N : ℤ := ⌈C⌉ with hN
  refine ((Set.finite_Icc (fun _ : Fin 3 => -N) (fun _ => N)).image
    (fun n : Fin 3 → ℤ => k.coordMap (fun i => (n i : ℝ) / 12))).subset ?_
  rintro x ⟨⟨n, rfl⟩, hx⟩
  refine ⟨n, ?_, rfl⟩
  have hxn : ‖k.coordMap (fun i => (n i : ℝ) / 12)‖ ≤ ‖c‖ + r := by
    have := Metric.mem_closedBall.1 hx
    have h2 := norm_le_of_mem_closedBall hx
    exact h2
  have hTx : T (k.coordMap (fun i => (n i : ℝ) / 12)) = fun i => (n i : ℝ) / 12 := by
    rw [hT, LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe, coordEquiv_symm_coordMap]
  have hb : ∀ i, |(n i : ℝ)| ≤ C := by
    intro i
    have h1 := norm_le_pi_norm (T (k.coordMap (fun i => (n i : ℝ) / 12))) i
    have h2 := T.le_opNorm (k.coordMap (fun i => (n i : ℝ) / 12))
    rw [hTx] at h1 h2
    have h3 : ‖T‖ * ‖k.coordMap (fun i => (n i : ℝ) / 12)‖ ≤ ‖T‖ * (‖c‖ + r) :=
      mul_le_mul_of_nonneg_left hxn (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_div] at h1
    rw [hC]
    have : |(n i : ℝ)| / |(12 : ℝ)| ≤ ‖T‖ * (‖c‖ + r) := by linarith
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 12)] at this
    linarith
  constructor
  · intro i
    have h := neg_abs_le (n i : ℝ)
    have hc := Int.le_ceil C
    have : (-(N : ℝ)) ≤ (n i : ℝ) := by rw [hN]; linarith [hb i]
    exact_mod_cast this
  · intro i
    have h := le_abs_self (n i : ℝ)
    have hc := Int.le_ceil C
    have : (n i : ℝ) ≤ (N : ℝ) := by rw [hN]; linarith [hb i]
    exact_mod_cast this

/-- the basis of `E 3` given by the lattice basis vectors -/
noncomputable def latBasis (k : LatticeKind) : Module.Basis (Fin 3) ℝ (E 3) :=
  (Pi.basisFun ℝ (Fin 3)).map (coordEquiv k)

lemma latBasis_apply (k : LatticeKind) (j : Fin 3) :
    latBasis k j = k.coordMap (Pi.single j 1) := by
  simp [latBasis]

lemma isom_ext_of_basis (k : LatticeKind) (g h : EuclideanIsom 3) (h0 : g 0 = h 0)
    (hj : ∀ j, g (latBasis k j) = h (latBasis k j)) : g = h := by
  have key : ∀ (f : EuclideanIsom 3) (v : E 3), f v = f.linearIsometryEquiv v + f 0 := by
    intro f v
    have := f.map_vadd 0 v
    simpa using this
  have hL : (g.linearIsometryEquiv : E 3 →ₗ[ℝ] E 3) = h.linearIsometryEquiv := by
    refine (latBasis k).ext fun j => ?_
    have h1 := key g (latBasis k j)
    have h2 := key h (latBasis k j)
    simp only [LinearEquiv.coe_coe]
    rw [hj j, h0] at h1
    rw [h1] at h2
    exact add_right_cancel h2
  ext1 x
  rw [key g x, key h x, h0]
  congr 1
  exact LinearMap.congr_fun hL x

lemma latBasis_mem_lat (k : LatticeKind) (j : Fin 3) : latBasis k j ∈ lat k := by
  refine ⟨Pi.single j 12, ?_⟩
  rw [latBasis_apply]
  congr 1
  funext i
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

lemma zero_mem_lat (k : LatticeKind) : (0 : E 3) ∈ lat k :=
  ⟨0, by simp only [Pi.zero_apply, Int.cast_zero, zero_div]; exact (map_zero k.coordMap).symm⟩

lemma latStab_discrete (k : LatticeKind) : IsDiscrete (latStab k) := by
  intro x ε hε
  let pts : Option (Fin 3) → E 3 := fun o => o.elim 0 (latBasis k)
  have hpts : ∀ o, pts o ∈ lat k := by
    intro o
    cases o with
    | none => exact zero_mem_lat k
    | some j => exact latBasis_mem_lat k j
  let F : EuclideanIsom 3 → (Option (Fin 3) → E 3) := fun g o => g (pts o)
  have hF : Function.Injective F := by
    intro g h hgh
    apply isom_ext_of_basis k g h (congrFun hgh none)
    intro j
    exact congrFun hgh (some j)
  let t : Option (Fin 3) → Set (E 3) :=
    fun o => lat k ∩ Metric.closedBall (pts o) (2 * dist (pts o) x + ε)
  have ht : (Set.pi Set.univ t).Finite :=
    Set.Finite.pi fun o => lat_inter_closedBall_finite k _ _
  refine (ht.preimage hF.injOn).subset ?_
  rintro g ⟨hg, hgx⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  intro o
  refine ⟨(hg (pts o)).1 (hpts o), ?_⟩
  rw [Metric.mem_closedBall]
  calc dist (g (pts o)) (pts o) ≤ dist (g (pts o)) (g x) + dist (g x) x + dist x (pts o) :=
        dist_triangle4 _ _ _ _
    _ = dist (pts o) x + dist (g x) x + dist (pts o) x := by
        rw [g.dist_map, dist_comm x]
    _ ≤ 2 * dist (pts o) x + ε := by linarith

lemma isDiscrete_of_le {G H : Subgroup (EuclideanIsom 3)} (hGH : G ≤ H) (hH : IsDiscrete H) :
    IsDiscrete G := by
  intro x ε hε
  exact (hH x ε hε).subset fun g hg => ⟨hGH hg.1, hg.2⟩


lemma SpaceGroupData.toIsom_mem (D : SpaceGroupData) {o : SymOp} (ho : o ∈ latticeOps ++ D.gens) :
    o.toIsom D.kind ∈ D.toSubgroup :=
  Subgroup.subset_closure ⟨o, ho, rfl⟩

lemma SpaceGroupData.le_latStab (D : SpaceGroupData)
    (hD : ∀ o ∈ latticeOps ++ D.gens, o.Compatible D.kind) : D.toSubgroup ≤ latStab D.kind := by
  rw [SpaceGroupData.toSubgroup, Subgroup.closure_le]
  rintro g ⟨o, ho, rfl⟩
  exact toIsom_mem_latStab (hD o ho)

lemma SpaceGroupData.translation_mem (D : SpaceGroupData)
    (hD : ∀ o ∈ latticeOps ++ D.gens, o.Compatible D.kind) (j : Fin 3) :
    ∃ g : EuclideanIsom 3, g ∈ D.toSubgroup ∧ IsTranslationBy g (latBasis D.kind j) := by
  fin_cases j
  · have ho : (⟨1, ![12, 0, 0]⟩ : SymOp) ∈ latticeOps ++ D.gens := by simp [latticeOps]
    refine ⟨_, D.toIsom_mem ho, fun x => ?_⟩
    obtain ⟨u, rfl⟩ := coordMap_surjective D.kind x
    rw [toIsom_coordMap (hD _ ho), latBasis_apply, ← map_add]
    congr 1
    funext i
    fin_cases i <;> simp [SymOp.coordAction]
  · have ho : (⟨1, ![0, 12, 0]⟩ : SymOp) ∈ latticeOps ++ D.gens := by simp [latticeOps]
    refine ⟨_, D.toIsom_mem ho, fun x => ?_⟩
    obtain ⟨u, rfl⟩ := coordMap_surjective D.kind x
    rw [toIsom_coordMap (hD _ ho), latBasis_apply, ← map_add]
    congr 1
    funext i
    fin_cases i <;> simp [SymOp.coordAction]
  · have ho : (⟨1, ![0, 0, 12]⟩ : SymOp) ∈ latticeOps ++ D.gens := by simp [latticeOps]
    refine ⟨_, D.toIsom_mem ho, fun x => ?_⟩
    obtain ⟨u, rfl⟩ := coordMap_surjective D.kind x
    rw [toIsom_coordMap (hD _ ho), latBasis_apply, ← map_add]
    congr 1
    funext i
    fin_cases i <;> simp [SymOp.coordAction]

theorem SpaceGroupData.isCrystallographic (D : SpaceGroupData)
    (hD : ∀ o ∈ latticeOps ++ D.gens, o.Compatible D.kind) :
    IsCrystallographicGroup D.toSubgroup where
  discrete := isDiscrete_of_le (D.le_latStab hD) (latStab_discrete D.kind)
  cocompact := ⟨latBasis D.kind, (latBasis D.kind).linearIndependent, D.translation_mem hD⟩


theorem catalog_isCrystallographic (i : Fin 230) :
    IsCrystallographicGroup (spaceGroupCatalog i) :=
  (catalogData i).isCrystallographic (catalogData_compatible i)

end LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog

open LeanEval.Geometry.SpaceGroupsProblem LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog in
theorem solution :
    ∀ i : Fin 230, IsCrystallographicGroup (spaceGroupCatalog i) :=
  catalog_isCrystallographic
