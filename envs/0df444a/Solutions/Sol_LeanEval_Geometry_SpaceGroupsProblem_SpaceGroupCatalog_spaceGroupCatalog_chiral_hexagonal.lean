-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog.spaceGroupCatalog_chiral_hexagonal
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T16:04:11.934611+00:00
-- url     : https://prove2.me/submissions/aac97e14-97d2-4c75-b8d6-89040ef3e671

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog




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




end LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog

namespace LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog
open Matrix

lemma SpaceGroupData.toIsom_mem (D : SpaceGroupData) {o : SymOp} (ho : o ∈ latticeOps ++ D.gens) :
    o.toIsom D.kind ∈ D.toSubgroup :=
  Subgroup.subset_closure ⟨o, ho, rfl⟩

lemma cast_mulVec_div (R : Matrix (Fin 3) (Fin 3) ℤ) (n : Fin 3 → ℤ) :
    R.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (n i : ℝ) / 12) = fun i => ((R *ᵥ n) i : ℝ) / 12 := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog




/-!
# Coordinate description of the catalogue groups

`HasCoordZ k x R m` says that the isometry `x` acts in the lattice coordinates of `k` as
`u ↦ R u + m / 12` with an integer matrix `R` and an integer vector `m`.  If a finite list of
operations is closed under composition and inversion modulo `ℤ³` and contains the generators of a
catalogue group, then every element of the group has this form with `(R, m mod 12)` in the list.
-/

namespace LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog
open Matrix

/-- the real vector `m / 12` of an integer vector `m` -/
noncomputable def v12 (m : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => (m i : ℝ) / 12

/-- the real matrix of an integer matrix -/
noncomputable abbrev rmat (R : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  R.map (Int.cast : ℤ → ℝ)

lemma rmat_mul (A B : Matrix (Fin 3) (Fin 3) ℤ) : rmat (A * B) = rmat A * rmat B := by
  have := (Int.castRingHom ℝ).mapMatrix.map_mul A B
  simpa using this

lemma rmat_one : rmat 1 = 1 :=
  Matrix.map_one _ Int.cast_zero Int.cast_one

lemma rmat_pow (A : Matrix (Fin 3) (Fin 3) ℤ) (j : ℕ) : rmat (A ^ j) = rmat A ^ j := by
  have := (Int.castRingHom ℝ).mapMatrix.map_pow A j
  simpa using this

lemma rmat_injective : Function.Injective rmat := by
  intro A B h
  ext i j
  have := congrFun (congrFun h i) j
  simpa using this

lemma rmat_mulVec_v12 (R : Matrix (Fin 3) (Fin 3) ℤ) (m : Fin 3 → ℤ) :
    rmat R *ᵥ v12 m = v12 (R *ᵥ m) := cast_mulVec_div R m

lemma v12_add (a b : Fin 3 → ℤ) : v12 (a + b) = v12 a + v12 b := by
  funext i; simp [v12]; ring

lemma v12_neg (a : Fin 3 → ℤ) : v12 (-a) = -v12 a := by
  funext i; simp [v12]; ring

lemma v12_zero : v12 0 = 0 := by
  funext i; simp [v12]

/-- `x` acts in the coordinates of `k` as `u ↦ R u + m / 12`. -/
def HasCoordZ (k : LatticeKind) (x : EuclideanIsom 3) (R : Matrix (Fin 3) (Fin 3) ℤ)
    (m : Fin 3 → ℤ) : Prop :=
  ∀ u : Fin 3 → ℝ, x (k.coordMap u) = k.coordMap (rmat R *ᵥ u + v12 m)

lemma HasCoordZ.mul {k : LatticeKind} {x y : EuclideanIsom 3} {Ra Rb : Matrix (Fin 3) (Fin 3) ℤ}
    {ma mb : Fin 3 → ℤ} (hx : HasCoordZ k x Ra ma) (hy : HasCoordZ k y Rb mb) :
    HasCoordZ k (x * y) (Ra * Rb) (Ra *ᵥ mb + ma) := by
  intro u
  show x (y (k.coordMap u)) = _
  rw [hy, hx, rmat_mul, v12_add, ← rmat_mulVec_v12, mulVec_add, mulVec_mulVec, add_assoc]

lemma HasCoordZ.one (k : LatticeKind) : HasCoordZ k 1 1 0 := by
  intro u
  simp [v12_zero]

lemma HasCoordZ.inv {k : LatticeKind} {x : EuclideanIsom 3} {R R' : Matrix (Fin 3) (Fin 3) ℤ}
    {m : Fin 3 → ℤ} (hx : HasCoordZ k x R m) (hR : R' * R = 1) :
    HasCoordZ k x⁻¹ R' (-(R' *ᵥ m)) := by
  intro u
  have hRR : R * R' = 1 := mul_eq_one_comm.1 hR
  have key : x (k.coordMap (rmat R' *ᵥ u + v12 (-(R' *ᵥ m)))) = k.coordMap u := by
    rw [hx]
    congr 1
    rw [v12_neg, ← rmat_mulVec_v12, mulVec_add, mulVec_neg, mulVec_mulVec, mulVec_mulVec,
      ← rmat_mul, hRR, rmat_one, one_mulVec, one_mulVec]
    abel
  rw [← key]
  simp

lemma HasCoordZ.pow {k : LatticeKind} {x : EuclideanIsom 3} {R : Matrix (Fin 3) (Fin 3) ℤ}
    {m : Fin 3 → ℤ} (hx : HasCoordZ k x R m) :
    ∀ j : ℕ, HasCoordZ k (x ^ j) (R ^ j) (∑ i ∈ Finset.range j, (R ^ i) *ᵥ m)
  | 0 => by simpa using HasCoordZ.one k
  | j + 1 => by
    have h := hx.mul (HasCoordZ.pow hx j)
    rw [pow_succ', pow_succ']
    convert h using 1
    rw [Finset.sum_range_succ', mulVec_sum]
    simp [mulVec_mulVec, pow_succ']

lemma HasCoordZ.toIsom {k : LatticeKind} {o : SymOp} (h : o.Compatible k) :
    HasCoordZ k (o.toIsom k) o.rot o.tr := by
  intro u
  rw [toIsom_coordMap h]
  rfl

lemma HasCoordZ.unique {k : LatticeKind} {x : EuclideanIsom 3} {R R' : Matrix (Fin 3) (Fin 3) ℤ}
    {m m' : Fin 3 → ℤ} (h : HasCoordZ k x R m) (h' : HasCoordZ k x R' m') : R = R' ∧ m = m' := by
  have hv : ∀ u, rmat R *ᵥ u + v12 m = rmat R' *ᵥ u + v12 m' := fun u =>
    coordMap_injective k ((h u).symm.trans (h' u))
  have hm : v12 m = v12 m' := by simpa using hv 0
  refine ⟨rmat_injective ?_, ?_⟩
  · ext i j
    have h1 : rmat R *ᵥ Pi.single j 1 = rmat R' *ᵥ Pi.single j 1 := by
      have := hv (Pi.single j 1)
      rw [hm] at this
      exact add_right_cancel this
    have := congrFun h1 i
    simpa [Matrix.mulVec_single_one] using this
  · funext i
    have := congrFun hm i
    simp only [v12] at this
    exact_mod_cast (by linarith : (m i : ℝ) = m' i)

/-- closure of an operation list modulo `ℤ³` -/
def OpsClosed (ops : List SymOp) : Prop :=
  (∀ a ∈ ops, ∀ b ∈ ops, ∃ c ∈ ops, c.rot = a.rot * b.rot ∧
      ∀ i, (12 : ℤ) ∣ (a.rot *ᵥ b.tr + a.tr - c.tr) i) ∧
  (∀ a ∈ ops, ∃ c ∈ ops, c.rot * a.rot = 1 ∧ ∀ i, (12 : ℤ) ∣ (c.rot *ᵥ a.tr + c.tr) i) ∧
  (∃ c ∈ ops, c.rot = 1 ∧ ∀ i, (12 : ℤ) ∣ c.tr i)

instance (ops : List SymOp) : Decidable (OpsClosed ops) := by
  unfold OpsClosed; infer_instance

/-- every generator lies in the operation list modulo `ℤ³` -/
def GensIn (ops gens : List SymOp) : Prop :=
  ∀ g ∈ gens, ∃ c ∈ ops, c.rot = g.rot ∧ ∀ i, (12 : ℤ) ∣ g.tr i - c.tr i

instance (ops gens : List SymOp) : Decidable (GensIn ops gens) := by
  unfold GensIn; infer_instance

/-- `x` is one of the operations of the list, up to an integer translation -/
def InOps (k : LatticeKind) (ops : List SymOp) (x : EuclideanIsom 3) : Prop :=
  ∃ o ∈ ops, ∃ m : Fin 3 → ℤ, (∀ i, (12 : ℤ) ∣ m i - o.tr i) ∧ HasCoordZ k x o.rot m

lemma dvd_mulVec {R : Matrix (Fin 3) (Fin 3) ℤ} {v : Fin 3 → ℤ} (h : ∀ i, (12 : ℤ) ∣ v i) (i : Fin 3) :
    (12 : ℤ) ∣ (R *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (h j) _

/-- the subgroup of isometries described by a closed operation list -/
noncomputable def opsSubgroup (k : LatticeKind) (ops : List SymOp) (h : OpsClosed ops) :
    Subgroup (EuclideanIsom 3) where
  carrier := {x | InOps k ops x}
  mul_mem' := by
    rintro x y ⟨a, ha, ma, hma, hx⟩ ⟨b, hb, mb, hmb, hy⟩
    obtain ⟨c, hc, hcr, hct⟩ := h.1 a ha b hb
    refine ⟨c, hc, a.rot *ᵥ mb + ma, fun i => ?_, hcr ▸ hx.mul hy⟩
    have e : (a.rot *ᵥ mb + ma - c.tr) i =
        (a.rot *ᵥ (mb - b.tr)) i + (a.rot *ᵥ b.tr + a.tr - c.tr) i + (ma i - a.tr i) := by
      simp [mulVec_sub]; ring
    have := e
    simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
    rw [this]
    exact dvd_add (dvd_add (dvd_mulVec (fun j => by simpa using hmb j) i) (by simpa using hct i))
      (hma i)
  one_mem' := by
    obtain ⟨c, hc, hcr, hct⟩ := h.2.2
    exact ⟨c, hc, 0, fun i => by simpa using (hct i), hcr ▸ HasCoordZ.one k⟩
  inv_mem' := by
    rintro x ⟨a, ha, ma, hma, hx⟩
    obtain ⟨c, hc, hcr, hct⟩ := h.2.1 a ha
    refine ⟨c, hc, -(c.rot *ᵥ ma), fun i => ?_, hx.inv hcr⟩
    have e : (-(c.rot *ᵥ ma) - c.tr) i = -((c.rot *ᵥ (ma - a.tr)) i + (c.rot *ᵥ a.tr + c.tr) i) := by
      simp [mulVec_sub]; ring
    simp only [Pi.sub_apply] at e ⊢
    rw [e]
    exact (dvd_add (dvd_mulVec (fun j => by simpa using hma j) i) (hct i)).neg_right

/-- **Structure theorem**: every element of a catalogue-style group is an operation of the list up
to an integer translation. -/
theorem SpaceGroupData.inOps_of_mem (D : SpaceGroupData) (ops : List SymOp) (hc : OpsClosed ops)
    (hg : GensIn ops (latticeOps ++ D.gens))
    (hD : ∀ o ∈ latticeOps ++ D.gens, o.Compatible D.kind) {x : EuclideanIsom 3}
    (hx : x ∈ D.toSubgroup) : InOps D.kind ops x := by
  have hle : D.toSubgroup ≤ opsSubgroup D.kind ops hc := by
    rw [SpaceGroupData.toSubgroup, Subgroup.closure_le]
    rintro g ⟨o, ho, rfl⟩
    obtain ⟨c, hcm, hcr, hct⟩ := hg o ho
    exact ⟨c, hcm, o.tr, fun i => hct i, hcr ▸ HasCoordZ.toIsom (hD o ho)⟩
  exact hle hx

/-- integer lattice translations belong to every catalogue group -/
theorem SpaceGroupData.exists_translation (D : SpaceGroupData)
    (hD : ∀ o ∈ latticeOps ++ D.gens, o.Compatible D.kind) (n : Fin 3 → ℤ) :
    ∃ x ∈ D.toSubgroup, HasCoordZ D.kind x 1 (12 • n) := by
  have hbasic : ∀ j : Fin 3, ∃ x ∈ D.toSubgroup,
      HasCoordZ D.kind x 1 (12 • Pi.single j (1 : ℤ)) := by
    intro j
    fin_cases j
    · have ho : (⟨1, ![12, 0, 0]⟩ : SymOp) ∈ latticeOps ++ D.gens := by simp [latticeOps]
      refine ⟨_, D.toIsom_mem ho, ?_⟩
      convert HasCoordZ.toIsom (hD _ ho) using 1
      funext i; fin_cases i <;> simp
    · have ho : (⟨1, ![0, 12, 0]⟩ : SymOp) ∈ latticeOps ++ D.gens := by simp [latticeOps]
      refine ⟨_, D.toIsom_mem ho, ?_⟩
      convert HasCoordZ.toIsom (hD _ ho) using 1
      funext i; fin_cases i <;> simp
    · have ho : (⟨1, ![0, 0, 12]⟩ : SymOp) ∈ latticeOps ++ D.gens := by simp [latticeOps]
      refine ⟨_, D.toIsom_mem ho, ?_⟩
      convert HasCoordZ.toIsom (hD _ ho) using 1
      funext i; fin_cases i <;> simp
  -- translations by integer vectors form a subgroup-like family closed under `+` and `-`
  have hadd : ∀ a b : Fin 3 → ℤ, (∃ x ∈ D.toSubgroup, HasCoordZ D.kind x 1 (12 • a)) →
      (∃ x ∈ D.toSubgroup, HasCoordZ D.kind x 1 (12 • b)) →
      ∃ x ∈ D.toSubgroup, HasCoordZ D.kind x 1 (12 • (a + b)) := by
    rintro a b ⟨x, hx, hxa⟩ ⟨y, hy, hyb⟩
    refine ⟨x * y, D.toSubgroup.mul_mem hx hy, ?_⟩
    have := hxa.mul hyb
    rw [one_mul, one_mulVec] at this
    rwa [smul_add, add_comm]
  have hneg : ∀ a : Fin 3 → ℤ, (∃ x ∈ D.toSubgroup, HasCoordZ D.kind x 1 (12 • a)) →
      ∃ x ∈ D.toSubgroup, HasCoordZ D.kind x 1 (12 • (-a)) := by
    rintro a ⟨x, hx, hxa⟩
    refine ⟨x⁻¹, D.toSubgroup.inv_mem hx, ?_⟩
    have := hxa.inv (R' := 1) (by simp)
    rwa [one_mulVec, ← smul_neg] at this
  have hsmul : ∀ (j : Fin 3) (z : ℤ), ∃ x ∈ D.toSubgroup,
      HasCoordZ D.kind x 1 (12 • (z • Pi.single j 1)) := by
    intro j z
    have h1 := hbasic j
    induction z using Int.induction_on with
    | zero => exact ⟨1, D.toSubgroup.one_mem, by simpa using HasCoordZ.one D.kind⟩
    | succ z ih =>
      obtain ⟨x, hx, h⟩ := hadd _ _ ih h1
      refine ⟨x, hx, ?_⟩
      convert h using 2
      funext i; simp; ring
    | pred z ih =>
      obtain ⟨x, hx, h⟩ := hadd _ _ ih (hneg _ h1)
      refine ⟨x, hx, ?_⟩
      convert h using 2
      funext i; simp; ring
  have hn : n = n 0 • Pi.single 0 1 + n 1 • Pi.single 1 1 + n 2 • Pi.single 2 1 := by
    funext i; fin_cases i <;> simp
  rw [hn]
  exact hadd _ _ (hadd _ _ (hsmul 0 _) (hsmul 1 _)) (hsmul 2 _)

end LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog




/-!
# Affine conjugation in lattice coordinates

An affine map `φ` of `E 3` is written in lattice coordinates (of `k₁` on the source and `k₂` on
the target) as `u ↦ M u + β`.  Conjugation of coordinate-described isometries then becomes the
usual matrix relations `M R = R' M` and `M t + β = R' β + t'`.
-/

namespace LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog
open Matrix

/-- the matrix of the linear part of `φ` in lattice coordinates -/
noncomputable def affMat (k₁ k₂ : LatticeKind) (φ : AffineGroup 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix' ((coordEquiv k₂).symm.toLinearMap ∘ₗ φ.linear.toLinearMap ∘ₗ
    (coordEquiv k₁).toLinearMap)

/-- the translation part of `φ` in lattice coordinates -/
noncomputable def affVec (k₂ : LatticeKind) (φ : AffineGroup 3) : Fin 3 → ℝ :=
  (coordEquiv k₂).symm (φ 0)

lemma aff_coord (k₁ k₂ : LatticeKind) (φ : AffineGroup 3) (u : Fin 3 → ℝ) :
    φ (k₁.coordMap u) = k₂.coordMap (affMat k₁ k₂ φ *ᵥ u + affVec k₂ φ) := by
  have h1 : φ (k₁.coordMap u) = φ.linear (k₁.coordMap u) + φ 0 := by
    have := φ.map_vadd 0 (k₁.coordMap u)
    simpa using this
  rw [h1, map_add, affMat, LinearMap.toMatrix'_mulVec, affVec]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  congr 1 <;> exact ((coordEquiv k₂).apply_symm_apply _).symm

lemma affine_form_unique {A B : Matrix (Fin 3) (Fin 3) ℝ} {a b : Fin 3 → ℝ}
    (h : ∀ u, A *ᵥ u + a = B *ᵥ u + b) : A = B ∧ a = b := by
  have hab : a = b := by simpa using h 0
  refine ⟨?_, hab⟩
  ext i j
  have h1 : A *ᵥ Pi.single j 1 = B *ᵥ Pi.single j 1 := by
    have := h (Pi.single j 1)
    rw [hab] at this
    exact add_right_cancel this
  have := congrFun h1 i
  simpa [Matrix.mulVec_single_one] using this

lemma affMat_mul (k₁ k₂ k₃ : LatticeKind) (φ ψ : AffineGroup 3) :
    affMat k₁ k₃ (φ * ψ) = affMat k₂ k₃ φ * affMat k₁ k₂ ψ := by
  have h : ∀ u, affMat k₁ k₃ (φ * ψ) *ᵥ u + affVec k₃ (φ * ψ) =
      (affMat k₂ k₃ φ * affMat k₁ k₂ ψ) *ᵥ u + (affMat k₂ k₃ φ *ᵥ affVec k₂ ψ + affVec k₃ φ) := by
    intro u
    apply coordMap_injective k₃
    rw [← aff_coord]
    show φ (ψ (k₁.coordMap u)) = _
    rw [aff_coord k₁ k₂, aff_coord k₂ k₃, mulVec_add, mulVec_mulVec, add_assoc]
  exact (affine_form_unique h).1

lemma affMat_one (k : LatticeKind) : affMat k k 1 = 1 := by
  have h : ∀ u, affMat k k 1 *ᵥ u + affVec k 1 = (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u + 0 := by
    intro u
    apply coordMap_injective k
    rw [← aff_coord]
    simp
  exact (affine_form_unique h).1

lemma affMat_inv_mul (k₁ k₂ : LatticeKind) (φ : AffineGroup 3) :
    affMat k₂ k₁ φ⁻¹ * affMat k₁ k₂ φ = 1 := by
  rw [← affMat_mul, inv_mul_cancel, affMat_one]

lemma affMat_mul_inv (k₁ k₂ : LatticeKind) (φ : AffineGroup 3) :
    affMat k₁ k₂ φ * affMat k₂ k₁ φ⁻¹ = 1 := by
  rw [← affMat_mul, mul_inv_cancel, affMat_one]

lemma det_affMat (k : LatticeKind) (φ : AffineGroup 3) :
    (affMat k k φ).det = (φ.linear.det : ℝ) := by
  rw [affMat, LinearMap.det_toMatrix', LinearEquiv.coe_det]
  have := LinearMap.det_conj (φ.linear.toLinearMap) (coordEquiv k).symm
  simpa using this

/-- **Conjugation in coordinates.** -/
lemma conj_coord {k₁ k₂ : LatticeKind} {φ : AffineGroup 3} {x y : EuclideanIsom 3}
    {R R' : Matrix (Fin 3) (Fin 3) ℤ} {m m' : Fin 3 → ℤ}
    (hx : HasCoordZ k₁ x R m) (hy : HasCoordZ k₂ y R' m')
    (h : y.toAffineEquiv = φ * x.toAffineEquiv * φ⁻¹) :
    affMat k₁ k₂ φ * rmat R = rmat R' * affMat k₁ k₂ φ ∧
      affMat k₁ k₂ φ *ᵥ v12 m + affVec k₂ φ = rmat R' *ᵥ affVec k₂ φ + v12 m' := by
  have h' : y.toAffineEquiv * φ = φ * x.toAffineEquiv := by rw [h]; group
  have key : ∀ u, (affMat k₁ k₂ φ * rmat R) *ᵥ u + (affMat k₁ k₂ φ *ᵥ v12 m + affVec k₂ φ) =
      (rmat R' * affMat k₁ k₂ φ) *ᵥ u + (rmat R' *ᵥ affVec k₂ φ + v12 m') := by
    intro u
    have e := congrArg (fun f : AffineGroup 3 => f (k₁.coordMap u)) h'
    simp only [AffineEquiv.coe_mul, Function.comp_apply,
      AffineIsometryEquiv.coe_toAffineEquiv] at e
    rw [aff_coord k₁ k₂, hy, hx, aff_coord k₁ k₂] at e
    have := coordMap_injective k₂ e
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    calc _ = affMat k₁ k₂ φ *ᵥ (rmat R *ᵥ u + v12 m) + affVec k₂ φ := by
            rw [mulVec_add]; abel
      _ = rmat R' *ᵥ (affMat k₁ k₂ φ *ᵥ u + affVec k₂ φ) + v12 m' := this.symm
      _ = _ := by rw [mulVec_add]; abel
  exact affine_form_unique key

end LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog




/-!
# The screw-sense invariant and the chirality of the enantiomorphic pairs

For an element `x` of a primitive catalogue group acting in lattice coordinates as
`u ↦ R u + t` where `R` has order exactly `n`, the power `x ^ n` is a lattice translation by an
integer vector `w`.  For integer vectors `v` the integer `det [v, R v, w]` is transported unchanged
by any conjugation whose linear part has determinant `1` on the lattice, which is the case for
orientation-preserving affine equivalences between primitive groups.  Its residues modulo `n` detect
the sense of the screw axes and separate each member of an enantiomorphic pair from the other.
-/

namespace LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog
open Matrix

/-! ### Algebraic preliminaries -/

/-- the matrix with columns `a`, `b`, `c` -/
def colMat {α : Type*} (a b c : Fin 3 → α) : Matrix (Fin 3) (Fin 3) α :=
  Matrix.of fun i j => ![a, b, c] j i

/-- explicit `3 × 3` determinant of the matrix with columns `a`, `b`, `c` -/
def det3 {α : Type*} [CommRing α] (a b c : Fin 3 → α) : α :=
  a 0 * b 1 * c 2 - a 0 * c 1 * b 2 - b 0 * a 1 * c 2 + b 0 * c 1 * a 2 + c 0 * a 1 * b 2 -
    c 0 * b 1 * a 2

lemma det_colMat {α : Type*} [CommRing α] (a b c : Fin 3 → α) :
    (colMat a b c).det = det3 a b c := by
  simp [colMat, det3, Matrix.det_fin_three]

lemma colMat_mulVec {α : Type*} [CommRing α] (A : Matrix (Fin 3) (Fin 3) α) (a b c : Fin 3 → α) :
    colMat (A *ᵥ a) (A *ᵥ b) (A *ᵥ c) = A * colMat a b c := by
  ext i j
  fin_cases j <;> simp [colMat, mulVec, dotProduct, Matrix.mul_apply]

lemma det3_mulVec {α : Type*} [CommRing α] (A : Matrix (Fin 3) (Fin 3) α) (a b c : Fin 3 → α) :
    det3 (A *ᵥ a) (A *ᵥ b) (A *ᵥ c) = A.det * det3 a b c := by
  rw [← det_colMat, colMat_mulVec, det_mul, det_colMat]

lemma det3_cast (n : ℕ) (a b c : Fin 3 → ℤ) :
    ((det3 a b c : ℤ) : ZMod n) = det3 (fun i => (a i : ZMod n)) (fun i => (b i : ZMod n))
      (fun i => (c i : ZMod n)) := by
  simp [det3]

lemma mulVec_cast (n : ℕ) (R : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) :
    (fun i => ((R *ᵥ v) i : ZMod n)) = R.map (Int.cast : ℤ → ZMod n) *ᵥ fun i => (v i : ZMod n) := by
  funext i
  simp [mulVec, dotProduct]

/-- `∑_{i<j} R^i`, computed recursively -/
def powMat (R : Matrix (Fin 3) (Fin 3) ℤ) : ℕ → Matrix (Fin 3) (Fin 3) ℤ
  | 0 => 0
  | j + 1 => R * powMat R j + 1

/-- the translation part `∑_{i<j} R^i m` of the `j`-th power of `u ↦ R u + m` -/
def powSum (R : Matrix (Fin 3) (Fin 3) ℤ) (m : Fin 3 → ℤ) : ℕ → Fin 3 → ℤ
  | 0 => 0
  | j + 1 => R *ᵥ powSum R m j + m

lemma powSum_eq (R : Matrix (Fin 3) (Fin 3) ℤ) (m : Fin 3 → ℤ) :
    ∀ j, powSum R m j = powMat R j *ᵥ m
  | 0 => by simp [powSum, powMat]
  | j + 1 => by
    rw [powSum, powMat, powSum_eq R m j, add_mulVec, mulVec_mulVec, one_mulVec]

lemma HasCoordZ.pow' {k : LatticeKind} {x : EuclideanIsom 3} {R : Matrix (Fin 3) (Fin 3) ℤ}
    {m : Fin 3 → ℤ} (hx : HasCoordZ k x R m) : ∀ j : ℕ, HasCoordZ k (x ^ j) (R ^ j) (powSum R m j)
  | 0 => by simpa [powSum] using HasCoordZ.one k
  | j + 1 => by
    rw [pow_succ', pow_succ']
    exact hx.mul (HasCoordZ.pow' hx j)

lemma toAffineEquiv_mul (x y : EuclideanIsom 3) :
    (x * y).toAffineEquiv = x.toAffineEquiv * y.toAffineEquiv := by
  ext z; rfl

lemma toAffineEquiv_pow (x : EuclideanIsom 3) :
    ∀ j : ℕ, (x ^ j).toAffineEquiv = x.toAffineEquiv ^ j
  | 0 => by ext z; rfl
  | j + 1 => by rw [pow_succ, pow_succ, toAffineEquiv_mul, toAffineEquiv_pow x j]

/-- `R` has order exactly `n` -/
def OrderIs (n : ℕ) (R : Matrix (Fin 3) (Fin 3) ℤ) : Prop :=
  R ^ n = 1 ∧ ∀ d ∈ List.range n, d ≠ 0 → R ^ d ≠ 1

instance (n : ℕ) (R : Matrix (Fin 3) (Fin 3) ℤ) : Decidable (OrderIs n R) := by
  unfold OrderIs; infer_instance

lemma pow_eq_one_iff_of_semiconj {A B M M' : Matrix (Fin 3) (Fin 3) ℤ} (h : M * A = B * M)
    (h1 : M' * M = 1) (h2 : M * M' = 1) (d : ℕ) : A ^ d = 1 ↔ B ^ d = 1 := by
  have hs : M * A ^ d = B ^ d * M := (SemiconjBy.pow_right h d)
  constructor
  · intro hA
    rw [hA, mul_one] at hs
    calc B ^ d = B ^ d * (M * M') := by rw [h2, mul_one]
      _ = M * M' := by rw [← mul_assoc, ← hs]
      _ = 1 := h2
  · intro hB
    rw [hB, one_mul] at hs
    calc A ^ d = (M' * M) * A ^ d := by rw [h1, one_mul]
      _ = M' * M := by rw [mul_assoc, hs]
      _ = 1 := h1

lemma orderIs_of_semiconj {A B M M' : Matrix (Fin 3) (Fin 3) ℤ} (h : M * A = B * M)
    (h1 : M' * M = 1) (h2 : M * M' = 1) (n : ℕ) (hB : OrderIs n B) : OrderIs n A := by
  refine ⟨(pow_eq_one_iff_of_semiconj h h1 h2 n).2 hB.1, fun d hd hd0 hA => ?_⟩
  exact hB.2 d hd hd0 ((pow_eq_one_iff_of_semiconj h h1 h2 d).1 hA)

/-! ### Lattice preservation -/

/-- a primitive operation list: the only pure translation is the identity -/
def Primitive (ops : List SymOp) : Prop := ∀ o ∈ ops, o.rot = 1 → o.tr = 0

instance (ops : List SymOp) : Decidable (Primitive ops) := by unfold Primitive; infer_instance

lemma v12_injective : Function.Injective v12 := by
  intro a b h
  funext i
  have := congrFun h i
  simp only [v12] at this
  exact_mod_cast (by linarith : (a i : ℝ) = b i)

lemma v12_smul12 (n : Fin 3 → ℤ) : v12 (12 • n) = fun i => (n i : ℝ) := by
  funext i; simp [v12]

/-- If conjugation by `ψ` maps every element of the catalogue group `D₁` into the primitive group
`D₂`, then the linear part of `ψ` maps lattice vectors to lattice vectors. -/
lemma affMat_integral (D₁ D₂ : SpaceGroupData) (ops₂ : List SymOp)
    (hc₂ : OpsClosed ops₂) (hg₂ : GensIn ops₂ (latticeOps ++ D₂.gens))
    (hD₁ : ∀ o ∈ latticeOps ++ D₁.gens, o.Compatible D₁.kind)
    (hD₂ : ∀ o ∈ latticeOps ++ D₂.gens, o.Compatible D₂.kind) (hp₂ : Primitive ops₂)
    (ψ : AffineGroup 3)
    (hψ : ∀ x ∈ D₁.toSubgroup, ∃ y ∈ D₂.toSubgroup, y.toAffineEquiv = ψ * x.toAffineEquiv * ψ⁻¹) :
    ∃ Mz : Matrix (Fin 3) (Fin 3) ℤ, affMat D₁.kind D₂.kind ψ = rmat Mz := by
  have hcol : ∀ n : Fin 3 → ℤ, ∃ n' : Fin 3 → ℤ,
      affMat D₁.kind D₂.kind ψ *ᵥ (fun i => (n i : ℝ)) = fun i => (n' i : ℝ) := by
    intro n
    obtain ⟨x, hx, hxc⟩ := D₁.exists_translation hD₁ n
    obtain ⟨y, hy, hyx⟩ := hψ x hx
    obtain ⟨o, ho, m, hm, hyc⟩ := D₂.inOps_of_mem ops₂ hc₂ hg₂ hD₂ hy
    obtain ⟨h1, h2⟩ := conj_coord hxc hyc hyx
    have hrot : o.rot = 1 := by
      apply rmat_injective
      rw [rmat_one]
      have := congrArg (· * affMat D₂.kind D₁.kind ψ⁻¹) h1
      simp only [rmat_one, mul_one, mul_assoc, affMat_mul_inv] at this
      exact this.symm
    have htr := hp₂ o ho hrot
    have hm' : ∀ i, (12 : ℤ) ∣ m i := fun i => by simpa [htr] using hm i
    choose q hq using hm'
    refine ⟨q, ?_⟩
    rw [hrot, rmat_one, one_mulVec, add_comm, add_left_cancel_iff, v12_smul12] at h2
    rw [h2]
    funext i
    simp [v12, hq i]
  choose f hf using hcol
  refine ⟨Matrix.of fun i j => f (Pi.single j 1) i, ?_⟩
  ext i j
  have := congrFun (hf (Pi.single j 1)) i
  simp only [Matrix.map_apply, Matrix.of_apply]
  rw [← this]
  have e : (fun i => ((Pi.single j (1 : ℤ) : Fin 3 → ℤ) i : ℝ)) = Pi.single j 1 := by
    funext l; by_cases hl : l = j
    · subst hl; simp
    · simp [hl]
  rw [e, Matrix.mulVec_single_one]
  rfl

/-! ### The screw check -/

/-- The finite check on an operation list: for every operation whose linear part `R` has order
exactly `n`, the `n`-th power is a lattice translation, `∑_{i<n} R^i ≡ 0 (mod n)`, and
`det [v, R v, w]` never takes the residue `r` modulo `n`. -/
def ScrewAvoids (n : ℕ) (r : ZMod n) (ops : List SymOp) : Prop :=
  ∀ o ∈ ops, OrderIs n o.rot → (∀ i, (12 : ℤ) ∣ powSum o.rot o.tr n i) ∧
    (powMat o.rot n).map (fun x => x % (n : ℤ)) = 0 ∧
    ∀ a b c : ZMod n,
      det3 ![a, b, c] (o.rot.map (Int.cast : ℤ → ZMod n) *ᵥ ![a, b, c])
        (fun i => ((powSum o.rot o.tr n i / 12 : ℤ) : ZMod n)) ≠ r

instance (n : ℕ) [NeZero n] (r : ZMod n) (ops : List SymOp) : Decidable (ScrewAvoids n r ops) := by
  unfold ScrewAvoids; infer_instance

lemma vec_eta {α : Type*} (v : Fin 3 → α) : v = ![v 0, v 1, v 2] := by
  funext i; fin_cases i <;> rfl

lemma ScrewAvoids.apply {n : ℕ} {r : ZMod n} {ops : List SymOp} (h : ScrewAvoids n r ops)
    {o : SymOp} (ho : o ∈ ops) (hord : OrderIs n o.rot) (k₁ v : Fin 3 → ℤ) :
    ((det3 v (o.rot *ᵥ v) (powSum o.rot o.tr n / 12 + powMat o.rot n *ᵥ k₁) : ℤ) : ZMod n) ≠ r := by
  obtain ⟨-, hN, hh⟩ := h o ho hord
  have hh := hh (v 0) (v 1) (v 2)
  rw [det3_cast]
  convert hh using 2
  · exact vec_eta _
  · rw [mulVec_cast]; congr 1; exact vec_eta _
  · funext i
    have hz : (((powMat o.rot n *ᵥ k₁) i : ℤ) : ZMod n) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [mulVec, dotProduct]
      refine Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero ?_) _
      have := congrFun (congrFun hN i) j
      simpa using this
    simp [hz]

/-! ### The chirality criterion -/

lemma mem_of_conj_set {G₁ G₂ : Subgroup (EuclideanIsom 3)} {φ : AffineGroup 3}
    (hφ : {h : AffineGroup 3 | ∃ g ∈ G₁, h = φ * g.toAffineEquiv * φ⁻¹} =
      {h : AffineGroup 3 | ∃ g ∈ G₂, h = g.toAffineEquiv}) :
    (∀ x ∈ G₁, ∃ y ∈ G₂, y.toAffineEquiv = φ * x.toAffineEquiv * φ⁻¹) ∧
      (∀ y ∈ G₂, ∃ x ∈ G₁, x.toAffineEquiv = φ⁻¹ * y.toAffineEquiv * φ⁻¹⁻¹) := by
  constructor
  · intro x hx
    have : φ * x.toAffineEquiv * φ⁻¹ ∈
        {h : AffineGroup 3 | ∃ g ∈ G₁, h = φ * g.toAffineEquiv * φ⁻¹} := ⟨x, hx, rfl⟩
    rw [hφ] at this
    obtain ⟨y, hy, e⟩ := this
    exact ⟨y, hy, e.symm⟩
  · intro y hy
    have : y.toAffineEquiv ∈ {h : AffineGroup 3 | ∃ g ∈ G₂, h = g.toAffineEquiv} := ⟨y, hy, rfl⟩
    rw [← hφ] at this
    obtain ⟨x, hx, e⟩ := this
    refine ⟨x, hx, ?_⟩
    rw [e]; group

/-- **Chirality criterion.**  Let `D₁`, `D₂` be primitive catalogue groups written in the same
lattice basis.  If `D₂` contains an element with an `n`-fold linear part whose screw residue at
`v = e₁` is `r`, while no element of `D₁` with an `n`-fold linear part ever attains the residue `r`,
then `D₁` and `D₂` are not orientation-preserving affinely equivalent. -/
theorem not_affOP_of_screw (D₁ D₂ : SpaceGroupData) (hk : D₁.kind = D₂.kind)
    (ops₁ ops₂ : List SymOp) (hc₁ : OpsClosed ops₁) (hc₂ : OpsClosed ops₂)
    (hg₁ : GensIn ops₁ (latticeOps ++ D₁.gens)) (hg₂ : GensIn ops₂ (latticeOps ++ D₂.gens))
    (hD₁ : ∀ o ∈ latticeOps ++ D₁.gens, o.Compatible D₁.kind)
    (hD₂ : ∀ o ∈ latticeOps ++ D₂.gens, o.Compatible D₂.kind)
    (hp₁ : Primitive ops₁) (hp₂ : Primitive ops₂)
    (n : ℕ) (r : ZMod n) (havoid : ScrewAvoids n r ops₁)
    (x₂ : EuclideanIsom 3) (hx₂ : x₂ ∈ D₂.toSubgroup) (R₂ : Matrix (Fin 3) (Fin 3) ℤ)
    (m₂ : Fin 3 → ℤ) (hxc : HasCoordZ D₂.kind x₂ R₂ m₂) (hord : OrderIs n R₂)
    (hdiv : ∀ i, (12 : ℤ) ∣ powSum R₂ m₂ n i)
    (hval : ((det3 (Pi.single 0 1) (R₂ *ᵥ Pi.single 0 1) (powSum R₂ m₂ n / 12) : ℤ) : ZMod n) = r) :
    ¬ AffOPEquivalent D₁.toSubgroup D₂.toSubgroup := by
  rintro ⟨φ, hdet, hφ⟩
  obtain ⟨hfw, hbw⟩ := mem_of_conj_set hφ
  -- integrality of the coordinate matrices of `φ` and `φ⁻¹`
  obtain ⟨Mz, hMz⟩ := affMat_integral D₁ D₂ ops₂ hc₂ hg₂ hD₁ hD₂ hp₂ φ hfw
  obtain ⟨Mz', hMz'⟩ := affMat_integral D₂ D₁ ops₁ hc₁ hg₁ hD₂ hD₁ hp₁ φ⁻¹ hbw
  have h1 : Mz' * Mz = 1 := by
    apply rmat_injective
    rw [rmat_mul, ← hMz, ← hMz', affMat_inv_mul, rmat_one]
  have h2 : Mz * Mz' = 1 := mul_eq_one_comm.1 h1
  -- `det Mz = 1`
  have hdetMz : Mz.det = 1 := by
    have hu : Mz'.det * Mz.det = 1 := by rw [← det_mul, h1, det_one]
    have hpos : (0 : ℝ) < (Mz.det : ℝ) := by
      have e : (Mz.det : ℝ) = (affMat D₁.kind D₁.kind φ).det := by
        rw [show affMat D₁.kind D₁.kind φ = affMat D₁.kind D₂.kind φ by rw [hk], hMz]
        exact (RingHom.map_det (Int.castRingHom ℝ) Mz)
      rw [e, det_affMat]; exact hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hu with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · rw [h] at hpos; norm_num at hpos
  -- pull the witness back to `D₁`
  obtain ⟨x₁, hx₁, hx₁e⟩ := hbw x₂ hx₂
  have hx₂e : x₂.toAffineEquiv = φ * x₁.toAffineEquiv * φ⁻¹ := by rw [hx₁e]; group
  obtain ⟨o, ho, m₁, hm₁, hx₁c⟩ := D₁.inOps_of_mem ops₁ hc₁ hg₁ hD₁ hx₁
  obtain ⟨hlin, -⟩ := conj_coord hx₁c hxc hx₂e
  rw [hMz, ← rmat_mul, ← rmat_mul] at hlin
  have hlinZ : Mz * o.rot = R₂ * Mz := rmat_injective hlin
  have hord₁ : OrderIs n o.rot := orderIs_of_semiconj hlinZ h1 h2 n hord
  -- the `n`-th powers are translations related by `Mz`
  have hpow₁ := hx₁c.pow' n
  have hpow₂ := hxc.pow' n
  rw [hord₁.1] at hpow₁
  rw [hord.1] at hpow₂
  have hpe : (x₂ ^ n).toAffineEquiv = φ * (x₁ ^ n).toAffineEquiv * φ⁻¹ := by
    rw [toAffineEquiv_pow, toAffineEquiv_pow, hx₂e, conj_pow]
  obtain ⟨-, htr⟩ := conj_coord hpow₁ hpow₂ hpe
  rw [rmat_one, one_mulVec, add_comm, add_left_cancel_iff, hMz, rmat_mulVec_v12] at htr
  have hS : Mz *ᵥ powSum o.rot m₁ n = powSum R₂ m₂ n := v12_injective htr
  -- write `m₁ = o.tr + 12 k₁`
  have hk₁ : ∀ i, ∃ q : ℤ, m₁ i - o.tr i = 12 * q := fun i => hm₁ i
  choose k₁ hk₁ using hk₁
  have hm₁e : m₁ = o.tr + 12 • k₁ := by funext i; simp; linarith [hk₁ i]
  obtain ⟨hdiv₁, -⟩ := havoid o ho hord₁
  set w₁ : Fin 3 → ℤ := powSum o.rot o.tr n / 12 + powMat o.rot n *ᵥ k₁ with hw₁
  set w₂ : Fin 3 → ℤ := powSum R₂ m₂ n / 12 with hw₂
  have hS₁ : powSum o.rot m₁ n = 12 • w₁ := by
    rw [powSum_eq, hm₁e, mulVec_add, mulVec_smul, ← powSum_eq, hw₁, smul_add]
    congr 1
    funext i
    simp only [Pi.smul_apply, Pi.div_apply]
    exact (Int.mul_ediv_cancel' (hdiv₁ i)).symm
  have hS₂ : powSum R₂ m₂ n = 12 • w₂ := by
    funext i
    simp only [Pi.smul_apply, hw₂, Pi.div_apply]
    exact (Int.mul_ediv_cancel' (hdiv i)).symm
  rw [hS₁, hS₂, mulVec_smul] at hS
  have hw : Mz *ᵥ w₁ = w₂ := by
    funext i
    have := congrFun hS i
    simp only [Pi.smul_apply] at this
    exact mul_left_cancel₀ (by norm_num : (12 : ℤ) ≠ 0) this
  clear_value w₁ w₂
  -- transport the determinant
  set v₁ : Fin 3 → ℤ := Mz' *ᵥ Pi.single 0 1 with hv₁
  have hv : Mz *ᵥ v₁ = Pi.single 0 1 := by rw [hv₁, mulVec_mulVec, h2, one_mulVec]
  clear_value v₁
  have hdet3 : det3 v₁ (o.rot *ᵥ v₁) w₁ = det3 (Pi.single 0 1) (R₂ *ᵥ Pi.single 0 1) w₂ := by
    have e2 : R₂ *ᵥ (Mz *ᵥ v₁) = Mz *ᵥ (o.rot *ᵥ v₁) := by
      rw [mulVec_mulVec, mulVec_mulVec, hlinZ]
    rw [← hv, ← hw, e2, det3_mulVec, hdetMz, one_mul]
  apply havoid.apply ho hord₁ k₁ v₁
  rw [← hw₁, hdet3]
  exact hval

end LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog

namespace LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog

/-- Operations of No. 169 modulo `ℤ³`. -/
def ops169 : List SymOp := [
  ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], ![0, 0, 0]⟩,
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], ![0, 0, 6]⟩,
  ⟨!![-1, 1, 0; -1, 0, 0; 0, 0, 1], ![0, 0, 8]⟩,
  ⟨!![0, -1, 0; 1, -1, 0; 0, 0, 1], ![0, 0, 4]⟩,
  ⟨!![0, 1, 0; -1, 1, 0; 0, 0, 1], ![0, 0, 10]⟩,
  ⟨!![1, -1, 0; 1, 0, 0; 0, 0, 1], ![0, 0, 2]⟩]

/-- Operations of No. 170 modulo `ℤ³`. -/
def ops170 : List SymOp := [
  ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], ![0, 0, 0]⟩,
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], ![0, 0, 6]⟩,
  ⟨!![-1, 1, 0; -1, 0, 0; 0, 0, 1], ![0, 0, 4]⟩,
  ⟨!![0, -1, 0; 1, -1, 0; 0, 0, 1], ![0, 0, 8]⟩,
  ⟨!![0, 1, 0; -1, 1, 0; 0, 0, 1], ![0, 0, 2]⟩,
  ⟨!![1, -1, 0; 1, 0, 0; 0, 0, 1], ![0, 0, 10]⟩]

/-- Operations of No. 171 modulo `ℤ³`. -/
def ops171 : List SymOp := [
  ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], ![0, 0, 0]⟩,
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], ![0, 0, 0]⟩,
  ⟨!![-1, 1, 0; -1, 0, 0; 0, 0, 1], ![0, 0, 4]⟩,
  ⟨!![0, -1, 0; 1, -1, 0; 0, 0, 1], ![0, 0, 8]⟩,
  ⟨!![0, 1, 0; -1, 1, 0; 0, 0, 1], ![0, 0, 8]⟩,
  ⟨!![1, -1, 0; 1, 0, 0; 0, 0, 1], ![0, 0, 4]⟩]

/-- Operations of No. 172 modulo `ℤ³`. -/
def ops172 : List SymOp := [
  ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], ![0, 0, 0]⟩,
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], ![0, 0, 0]⟩,
  ⟨!![-1, 1, 0; -1, 0, 0; 0, 0, 1], ![0, 0, 8]⟩,
  ⟨!![0, -1, 0; 1, -1, 0; 0, 0, 1], ![0, 0, 4]⟩,
  ⟨!![0, 1, 0; -1, 1, 0; 0, 0, 1], ![0, 0, 4]⟩,
  ⟨!![1, -1, 0; 1, 0, 0; 0, 0, 1], ![0, 0, 8]⟩]

/-- Operations of No. 178 modulo `ℤ³`. -/
def ops178 : List SymOp := [
  ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], ![0, 0, 0]⟩,
  ⟨!![-1, 0, 0; -1, 1, 0; 0, 0, -1], ![0, 0, 8]⟩,
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], ![0, 0, 6]⟩,
  ⟨!![-1, 1, 0; -1, 0, 0; 0, 0, 1], ![0, 0, 8]⟩,
  ⟨!![-1, 1, 0; 0, 1, 0; 0, 0, -1], ![0, 0, 6]⟩,
  ⟨!![0, -1, 0; -1, 0, 0; 0, 0, -1], ![0, 0, 10]⟩,
  ⟨!![0, -1, 0; 1, -1, 0; 0, 0, 1], ![0, 0, 4]⟩,
  ⟨!![0, 1, 0; -1, 1, 0; 0, 0, 1], ![0, 0, 10]⟩,
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], ![0, 0, 4]⟩,
  ⟨!![1, -1, 0; 0, -1, 0; 0, 0, -1], ![0, 0, 0]⟩,
  ⟨!![1, -1, 0; 1, 0, 0; 0, 0, 1], ![0, 0, 2]⟩,
  ⟨!![1, 0, 0; 1, -1, 0; 0, 0, -1], ![0, 0, 2]⟩]

/-- Operations of No. 179 modulo `ℤ³`. -/
def ops179 : List SymOp := [
  ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], ![0, 0, 0]⟩,
  ⟨!![-1, 0, 0; -1, 1, 0; 0, 0, -1], ![0, 0, 4]⟩,
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], ![0, 0, 6]⟩,
  ⟨!![-1, 1, 0; -1, 0, 0; 0, 0, 1], ![0, 0, 4]⟩,
  ⟨!![-1, 1, 0; 0, 1, 0; 0, 0, -1], ![0, 0, 6]⟩,
  ⟨!![0, -1, 0; -1, 0, 0; 0, 0, -1], ![0, 0, 2]⟩,
  ⟨!![0, -1, 0; 1, -1, 0; 0, 0, 1], ![0, 0, 8]⟩,
  ⟨!![0, 1, 0; -1, 1, 0; 0, 0, 1], ![0, 0, 2]⟩,
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], ![0, 0, 8]⟩,
  ⟨!![1, -1, 0; 0, -1, 0; 0, 0, -1], ![0, 0, 0]⟩,
  ⟨!![1, -1, 0; 1, 0, 0; 0, 0, 1], ![0, 0, 10]⟩,
  ⟨!![1, 0, 0; 1, -1, 0; 0, 0, -1], ![0, 0, 10]⟩]

/-- Operations of No. 180 modulo `ℤ³`. -/
def ops180 : List SymOp := [
  ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], ![0, 0, 0]⟩,
  ⟨!![-1, 0, 0; -1, 1, 0; 0, 0, -1], ![0, 0, 4]⟩,
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], ![0, 0, 0]⟩,
  ⟨!![-1, 1, 0; -1, 0, 0; 0, 0, 1], ![0, 0, 4]⟩,
  ⟨!![-1, 1, 0; 0, 1, 0; 0, 0, -1], ![0, 0, 0]⟩,
  ⟨!![0, -1, 0; -1, 0, 0; 0, 0, -1], ![0, 0, 8]⟩,
  ⟨!![0, -1, 0; 1, -1, 0; 0, 0, 1], ![0, 0, 8]⟩,
  ⟨!![0, 1, 0; -1, 1, 0; 0, 0, 1], ![0, 0, 8]⟩,
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], ![0, 0, 8]⟩,
  ⟨!![1, -1, 0; 0, -1, 0; 0, 0, -1], ![0, 0, 0]⟩,
  ⟨!![1, -1, 0; 1, 0, 0; 0, 0, 1], ![0, 0, 4]⟩,
  ⟨!![1, 0, 0; 1, -1, 0; 0, 0, -1], ![0, 0, 4]⟩]

/-- Operations of No. 181 modulo `ℤ³`. -/
def ops181 : List SymOp := [
  ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], ![0, 0, 0]⟩,
  ⟨!![-1, 0, 0; -1, 1, 0; 0, 0, -1], ![0, 0, 8]⟩,
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], ![0, 0, 0]⟩,
  ⟨!![-1, 1, 0; -1, 0, 0; 0, 0, 1], ![0, 0, 8]⟩,
  ⟨!![-1, 1, 0; 0, 1, 0; 0, 0, -1], ![0, 0, 0]⟩,
  ⟨!![0, -1, 0; -1, 0, 0; 0, 0, -1], ![0, 0, 4]⟩,
  ⟨!![0, -1, 0; 1, -1, 0; 0, 0, 1], ![0, 0, 4]⟩,
  ⟨!![0, 1, 0; -1, 1, 0; 0, 0, 1], ![0, 0, 4]⟩,
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], ![0, 0, 4]⟩,
  ⟨!![1, -1, 0; 0, -1, 0; 0, 0, -1], ![0, 0, 0]⟩,
  ⟨!![1, -1, 0; 1, 0, 0; 0, 0, 1], ![0, 0, 8]⟩,
  ⟨!![1, 0, 0; 1, -1, 0; 0, 0, -1], ![0, 0, 8]⟩]

end LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog

namespace LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- No. 169 and No. 170 are not orientation-preserving affinely equivalent. -/
theorem chiral_169_170 : ¬ AffOPEquivalent (spaceGroupCatalog 168) (spaceGroupCatalog 169) := by
  have hD₁ : ∀ o ∈ latticeOps ++ (catalogData 168).gens, o.Compatible (catalogData 168).kind := by
    decide +kernel
  have hD₂ : ∀ o ∈ latticeOps ++ (catalogData 169).gens, o.Compatible (catalogData 169).kind := by
    decide +kernel
  have ho : (SymOp.mirror ⟨!![1, -1, 0; 1, 0, 0; 0, 0, 1], ![0, 0, 2]⟩) ∈ latticeOps ++ (catalogData 169).gens := by decide +kernel
  have hx := (catalogData 169).toSubgroup.mul_mem ((catalogData 169).toIsom_mem ho)
    ((catalogData 169).toIsom_mem ho)
  have hc := (HasCoordZ.toIsom (hD₂ _ ho)).mul (HasCoordZ.toIsom (hD₂ _ ho))
  exact not_affOP_of_screw (catalogData 168) (catalogData 169) rfl ops169 ops170
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hD₁ hD₂
    (by decide +kernel) (by decide +kernel) 3 2 (by decide +kernel) _ hx _ _ hc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- No. 171 and No. 172 are not orientation-preserving affinely equivalent. -/
theorem chiral_171_172 : ¬ AffOPEquivalent (spaceGroupCatalog 170) (spaceGroupCatalog 171) := by
  have hD₁ : ∀ o ∈ latticeOps ++ (catalogData 170).gens, o.Compatible (catalogData 170).kind := by
    decide +kernel
  have hD₂ : ∀ o ∈ latticeOps ++ (catalogData 171).gens, o.Compatible (catalogData 171).kind := by
    decide +kernel
  have ho : (SymOp.mirror ⟨!![1, -1, 0; 1, 0, 0; 0, 0, 1], ![0, 0, 4]⟩) ∈ latticeOps ++ (catalogData 171).gens := by decide +kernel
  have hx := (catalogData 171).toSubgroup.mul_mem ((catalogData 171).toIsom_mem ho)
    ((catalogData 171).toIsom_mem ho)
  have hc := (HasCoordZ.toIsom (hD₂ _ ho)).mul (HasCoordZ.toIsom (hD₂ _ ho))
  exact not_affOP_of_screw (catalogData 170) (catalogData 171) rfl ops171 ops172
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hD₁ hD₂
    (by decide +kernel) (by decide +kernel) 3 1 (by decide +kernel) _ hx _ _ hc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- No. 178 and No. 179 are not orientation-preserving affinely equivalent. -/
theorem chiral_178_179 : ¬ AffOPEquivalent (spaceGroupCatalog 177) (spaceGroupCatalog 178) := by
  have hD₁ : ∀ o ∈ latticeOps ++ (catalogData 177).gens, o.Compatible (catalogData 177).kind := by
    decide +kernel
  have hD₂ : ∀ o ∈ latticeOps ++ (catalogData 178).gens, o.Compatible (catalogData 178).kind := by
    decide +kernel
  have ho : (SymOp.mirror ⟨!![1, -1, 0; 1, 0, 0; 0, 0, 1], ![0, 0, 2]⟩) ∈ latticeOps ++ (catalogData 178).gens := by decide +kernel
  have hx := (catalogData 178).toSubgroup.mul_mem ((catalogData 178).toIsom_mem ho)
    ((catalogData 178).toIsom_mem ho)
  have hc := (HasCoordZ.toIsom (hD₂ _ ho)).mul (HasCoordZ.toIsom (hD₂ _ ho))
  exact not_affOP_of_screw (catalogData 177) (catalogData 178) rfl ops178 ops179
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hD₁ hD₂
    (by decide +kernel) (by decide +kernel) 3 2 (by decide +kernel) _ hx _ _ hc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- No. 180 and No. 181 are not orientation-preserving affinely equivalent. -/
theorem chiral_180_181 : ¬ AffOPEquivalent (spaceGroupCatalog 179) (spaceGroupCatalog 180) := by
  have hD₁ : ∀ o ∈ latticeOps ++ (catalogData 179).gens, o.Compatible (catalogData 179).kind := by
    decide +kernel
  have hD₂ : ∀ o ∈ latticeOps ++ (catalogData 180).gens, o.Compatible (catalogData 180).kind := by
    decide +kernel
  have ho : (SymOp.mirror ⟨!![1, -1, 0; 1, 0, 0; 0, 0, 1], ![0, 0, 4]⟩) ∈ latticeOps ++ (catalogData 180).gens := by decide +kernel
  have hx := (catalogData 180).toSubgroup.mul_mem ((catalogData 180).toIsom_mem ho)
    ((catalogData 180).toIsom_mem ho)
  have hc := (HasCoordZ.toIsom (hD₂ _ ho)).mul (HasCoordZ.toIsom (hD₂ _ ho))
  exact not_affOP_of_screw (catalogData 179) (catalogData 180) rfl ops180 ops181
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hD₁ hD₂
    (by decide +kernel) (by decide +kernel) 3 1 (by decide +kernel) _ hx _ _ hc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)


end LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog

open LeanEval.Geometry.SpaceGroupsProblem LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog in
theorem solution :
    ¬ AffOPEquivalent (spaceGroupCatalog 168) (spaceGroupCatalog 169) ∧
      ¬ AffOPEquivalent (spaceGroupCatalog 170) (spaceGroupCatalog 171) ∧
      ¬ AffOPEquivalent (spaceGroupCatalog 177) (spaceGroupCatalog 178) ∧
      ¬ AffOPEquivalent (spaceGroupCatalog 179) (spaceGroupCatalog 180) :=
  ⟨chiral_169_170, chiral_171_172, chiral_178_179, chiral_180_181⟩
