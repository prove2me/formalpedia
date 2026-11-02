-- Prove2me | solution 1 for HarlowTASI.ewr_duality_imp_factorization
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:59:54.15683+00:00
-- url     : https://prove2.me/submissions/05ec37d3-d3d1-4b37-bb2a-6b54e061df2a

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras
import Theorems.Thm_HarlowTASI_centralizer_blockAlgebraLeft

set_option linter.unusedSectionVars false

open Matrix
open scoped Kronecker ComplexInnerProductSpace

namespace HarlowTASI

noncomputable def toE {R : Type} [Fintype R] (v : R → ℂ) : EuclideanSpace ℂ R :=
  WithLp.toLp 2 v

lemma inner_toE {R : Type} [Fintype R] (u v : R → ℂ) :
    inner ℂ (toE u) (toE v) = ∑ r, star (u r) * v r := by
  simp [toE, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  ac_rfl

lemma sub_onb_sum {R : Type} [Fintype R] [DecidableEq R]
    (S : Submodule ℂ (EuclideanSpace ℂ R)) (u : R → ℂ) (hu : toE u ∈ S) (r : R) :
    let b := stdOrthonormalBasis ℂ S
    u r = ∑ k : Fin (Module.finrank ℂ S),
      (∑ r' : R, star (((b k : S) : EuclideanSpace ℂ R).ofLp r') * u r') *
        (((b k : S) : EuclideanSpace ℂ R).ofLp r) := by
  intro b
  have h1 := b.sum_repr ⟨toE u, hu⟩
  have h2 := congr_arg (fun x : S => (x : EuclideanSpace ℂ R).ofLp r) h1
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    OrthonormalBasis.repr_apply_apply, toE] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [Submodule.coe_inner]
  change inner ℂ (toE (((b k : S) : EuclideanSpace ℂ R).ofLp)) (toE u) = _
  rw [inner_toE]

lemma sub_onb_ortho {R : Type} [Fintype R] [DecidableEq R]
    (S : Submodule ℂ (EuclideanSpace ℂ R))
    (k k' : Fin (Module.finrank ℂ S)) :
    let b := stdOrthonormalBasis ℂ S
    ∑ r : R, star (((b k : S) : EuclideanSpace ℂ R).ofLp r) *
      (((b k' : S) : EuclideanSpace ℂ R).ofLp r) = if k = k' then 1 else 0 := by
  intro b
  have h := b.inner_eq_ite k k'
  rw [Submodule.coe_inner] at h
  rw [← h]
  exact (inner_toE _ _).symm

section MatrixLemmas
variable {R Rb : Type} [Fintype R] [DecidableEq R] [Fintype Rb] [DecidableEq Rb]
variable {N : ℕ} {dr drb : Fin N → ℕ}

lemma kronecker_one_mul_apply (OR : Matrix R R ℂ)
    (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ) (x : R) (y : Rb)
    (p : BlockIndex N dr drb) :
    ((OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W) (x, y) p = ∑ x' : R, OR x x' * W (x', y) p := by
  rw [mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Finset.sum_eq_single y]
  · simp [kroneckerMap_apply]
  · intro y' _ hy'
    simp [kroneckerMap_apply, one_apply_ne (Ne.symm hy')]
  · intro hy; exact (hy (Finset.mem_univ y)).elim

lemma one_kronecker_mul_apply (ORb : Matrix Rb Rb ℂ)
    (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ) (x : R) (y : Rb)
    (p : BlockIndex N dr drb) :
    (((1 : Matrix R R ℂ) ⊗ₖ ORb) * W) (x, y) p = ∑ y' : Rb, ORb y y' * W (x, y') p := by
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [Finset.sum_eq_single x]
  · simp [kroneckerMap_apply]
  · intro x' _ hx'
    simp [kroneckerMap_apply, one_apply_ne (Ne.symm hx')]
  · intro hx; exact (hx (Finset.mem_univ x)).elim

lemma mul_blockLeftOp_apply (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (x : ∀ b, Matrix (Fin (dr b)) (Fin (dr b)) ℂ) (xy : R × Rb)
    (a' : Fin N) (i' : Fin (dr a')) (j' : Fin (drb a')) :
    (W * blockLeftOp (drb := drb) x) xy ⟨a', (i', j')⟩ =
      ∑ r : Fin (dr a'), W xy ⟨a', (r, j')⟩ * x a' r i' := by
  rw [mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single a']
  · simp only [blockLeftOp, blockDiagonal'_apply_eq]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single j']
    · simp [kroneckerMap_apply]
    · intro s _ hs
      simp [kroneckerMap_apply, one_apply_ne hs]
    · intro hj'; exact (hj' (Finset.mem_univ j')).elim
  · intro b _ hb
    refine Finset.sum_eq_zero fun rs _ => ?_
    simp [blockLeftOp, blockDiagonal'_apply_ne _ _ _ hb]
  · intro ha'; exact (ha' (Finset.mem_univ a')).elim

lemma mul_blockLeftOp_conjTranspose_apply (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (x : ∀ b, Matrix (Fin (dr b)) (Fin (dr b)) ℂ) (xy : R × Rb)
    (a' : Fin N) (i' : Fin (dr a')) (j' : Fin (drb a')) :
    (W * (blockLeftOp (drb := drb) x)ᴴ) xy ⟨a', (i', j')⟩ =
      ∑ r : Fin (dr a'), W xy ⟨a', (r, j')⟩ * star (x a' i' r) := by
  rw [mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single a']
  · simp only [blockLeftOp, conjTranspose_apply, blockDiagonal'_apply_eq]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single j']
    · simp [kroneckerMap_apply]
    · intro s _ hs
      simp [kroneckerMap_apply, one_apply_ne (Ne.symm hs)]
    · intro hj'; exact (hj' (Finset.mem_univ j')).elim
  · intro b _ hb
    refine Finset.sum_eq_zero fun rs _ => ?_
    simp [blockLeftOp, conjTranspose_apply, blockDiagonal'_apply_ne _ _ _ (Ne.symm hb)]
  · intro ha'; exact (ha' (Finset.mem_univ a')).elim

lemma mul_blockRightOp_apply (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (y : ∀ b, Matrix (Fin (drb b)) (Fin (drb b)) ℂ) (xy : R × Rb)
    (a' : Fin N) (i' : Fin (dr a')) (j' : Fin (drb a')) :
    (W * blockRightOp (dr := dr) y) xy ⟨a', (i', j')⟩ =
      ∑ s : Fin (drb a'), W xy ⟨a', (i', s)⟩ * y a' s j' := by
  rw [mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single a']
  · simp only [blockRightOp, blockDiagonal'_apply_eq]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single i']
    · simp [kroneckerMap_apply]
    · intro r _ hr
      simp [kroneckerMap_apply, one_apply_ne hr]
    · intro hi'; exact (hi' (Finset.mem_univ i')).elim
  · intro b _ hb
    refine Finset.sum_eq_zero fun rs _ => ?_
    simp [blockRightOp, blockDiagonal'_apply_ne _ _ _ hb]
  · intro ha'; exact (ha' (Finset.mem_univ a')).elim

lemma mul_blockRightOp_conjTranspose_apply (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (y : ∀ b, Matrix (Fin (drb b)) (Fin (drb b)) ℂ) (xy : R × Rb)
    (a' : Fin N) (i' : Fin (dr a')) (j' : Fin (drb a')) :
    (W * (blockRightOp (dr := dr) y)ᴴ) xy ⟨a', (i', j')⟩ =
      ∑ s : Fin (drb a'), W xy ⟨a', (i', s)⟩ * star (y a' j' s) := by
  rw [mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single a']
  · simp only [blockRightOp, conjTranspose_apply, blockDiagonal'_apply_eq]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single i']
    · simp [kroneckerMap_apply]
    · intro r _ hr
      simp [kroneckerMap_apply, one_apply_ne (Ne.symm hr)]
    · intro hi'; exact (hi' (Finset.mem_univ i')).elim
  · intro b _ hb
    refine Finset.sum_eq_zero fun rs _ => ?_
    simp [blockRightOp, conjTranspose_apply, blockDiagonal'_apply_ne _ _ _ (Ne.symm hb)]
  · intro ha'; exact (ha' (Finset.mem_univ a')).elim

def leftUnit (a : Fin N) (i : Fin (dr a)) : ∀ b, Matrix (Fin (dr b)) (Fin (dr b)) ℂ :=
  fun b r c => if b = a ∧ r.1 = i.1 ∧ c.1 = 0 then 1 else 0

def rightUnit (a : Fin N) (j : Fin (drb a)) : ∀ b, Matrix (Fin (drb b)) (Fin (drb b)) ℂ :=
  fun b r c => if b = a ∧ r.1 = j.1 ∧ c.1 = 0 then 1 else 0

lemma sum_leftUnit_eq (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (a : Fin N) (i i0 : Fin (dr a)) (hi0 : i0.1 = 0) (j : Fin (drb a)) (xy : R × Rb) :
    ∑ r : Fin (dr a), W xy ⟨a, (r, j)⟩ * leftUnit (dr := dr) a i a r i0 = W xy ⟨a, (i, j)⟩ := by
  rw [Finset.sum_eq_single i]
  · simp [leftUnit, hi0]
  · intro r _ hr
    have hrval : r.1 ≠ i.1 := fun h => hr (Fin.ext h)
    simp [leftUnit, hrval]
  · intro hi; exact (hi (Finset.mem_univ i)).elim

lemma sum_star_leftUnit_eq (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (a a' : Fin N) (i : Fin (dr a)) (i' i0' : Fin (dr a')) (hi0' : i0'.1 = 0)
    (j' : Fin (drb a')) (xy : R × Rb) :
    ∑ r : Fin (dr a'), W xy ⟨a', (r, j')⟩ * star (leftUnit (dr := dr) a i a' i' r) =
      if a' = a ∧ i'.1 = i.1 then W xy ⟨a', (i0', j')⟩ else 0 := by
  split_ifs with h
  · rcases h with ⟨rfl, hi'⟩
    rw [Finset.sum_eq_single i0']
    · simp [leftUnit, hi', hi0']
    · intro r _ hr
      have hr0 : r.1 ≠ 0 := by
        intro h0
        apply hr
        exact Fin.ext (h0.trans hi0'.symm)
      simp [leftUnit, hr0]
    · intro hi0; exact (hi0 (Finset.mem_univ i0')).elim
  · refine Finset.sum_eq_zero fun r _ => ?_
    have hnot : ¬ (a' = a ∧ i'.1 = i.1 ∧ r.1 = 0) := fun ⟨h1, h2, _⟩ => h ⟨h1, h2⟩
    simp [leftUnit, hnot]

lemma sum_rightUnit_eq (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (a : Fin N) (i : Fin (dr a)) (j j0 : Fin (drb a)) (hj0 : j0.1 = 0) (xy : R × Rb) :
    ∑ s : Fin (drb a), W xy ⟨a, (i, s)⟩ * rightUnit (drb := drb) a j a s j0 = W xy ⟨a, (i, j)⟩ := by
  rw [Finset.sum_eq_single j]
  · simp [rightUnit, hj0]
  · intro s _ hs
    have hsval : s.1 ≠ j.1 := fun h => hs (Fin.ext h)
    simp [rightUnit, hsval]
  · intro hj; exact (hj (Finset.mem_univ j)).elim

lemma sum_star_rightUnit_eq (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (a a' : Fin N) (j : Fin (drb a)) (i' : Fin (dr a')) (j' j0' : Fin (drb a')) (hj0' : j0'.1 = 0)
    (xy : R × Rb) :
    ∑ s : Fin (drb a'), W xy ⟨a', (i', s)⟩ * star (rightUnit (drb := drb) a j a' j' s) =
      if a' = a ∧ j'.1 = j.1 then W xy ⟨a', (i', j0')⟩ else 0 := by
  split_ifs with h
  · rcases h with ⟨rfl, hj'⟩
    rw [Finset.sum_eq_single j0']
    · simp [rightUnit, hj', hj0']
    · intro s _ hs
      have hs0 : s.1 ≠ 0 := by
        intro h0
        apply hs
        exact Fin.ext (h0.trans hj0'.symm)
      simp [rightUnit, hs0]
    · intro hj0; exact (hj0 (Finset.mem_univ j0')).elim
  · refine Finset.sum_eq_zero fun s _ => ?_
    have hnot : ¬ (a' = a ∧ j'.1 = j.1 ∧ s.1 = 0) := fun ⟨h1, h2, _⟩ => h ⟨h1, h2⟩
    simp [rightUnit, hnot]

def genR (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ) (a : Fin N) :
    Set (EuclideanSpace ℂ R) :=
  { u | ∃ (y : Rb) (i0 : Fin (dr a)) (j0 : Fin (drb a)),
    i0.1 = 0 ∧ j0.1 = 0 ∧ u = toE (fun x => W (x, y) ⟨a, (i0, j0)⟩) }

def SR (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ) (a : Fin N) :
    Submodule ℂ (EuclideanSpace ℂ R) :=
  Submodule.span ℂ (genR W a)

def genRb (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ) (a : Fin N) :
    Set (EuclideanSpace ℂ Rb) :=
  { v | ∃ (x : R) (i0 : Fin (dr a)) (j0 : Fin (drb a)),
    i0.1 = 0 ∧ j0.1 = 0 ∧ v = toE (fun y => W (x, y) ⟨a, (i0, j0)⟩) }

def SRb (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ) (a : Fin N) :
    Submodule ℂ (EuclideanSpace ℂ Rb) :=
  Submodule.span ℂ (genRb W a)

lemma A_mulVec_slice (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (A : ∀ a, Fin (dr a) → Matrix R R ℂ)
    (hA1 : ∀ a i, (A a i ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W =
      W * blockLeftOp (drb := drb) (leftUnit (dr := dr) a i))
    (a : Fin N) (i i0 : Fin (dr a)) (hi0 : i0.1 = 0) (j : Fin (drb a)) (y : Rb) :
    A a i *ᵥ (fun x => W (x, y) ⟨a, (i0, j)⟩) = fun x => W (x, y) ⟨a, (i, j)⟩ := by
  ext x
  change ∑ x', A a i x x' * W (x', y) ⟨a, (i0, j)⟩ = _
  rw [← kronecker_one_mul_apply, hA1 a i, mul_blockLeftOp_apply,
    sum_leftUnit_eq W a i i0 hi0 j (x, y)]

lemma A_conjTranspose_mulVec_slice (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (A : ∀ a, Fin (dr a) → Matrix R R ℂ)
    (hA2 : ∀ a i, ((A a i)ᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W =
      W * (blockLeftOp (drb := drb) (leftUnit (dr := dr) a i))ᴴ)
    (a a' : Fin N) (i : Fin (dr a)) (i' i0' : Fin (dr a')) (hi0' : i0'.1 = 0)
    (j' : Fin (drb a')) (y : Rb) :
    (A a i)ᴴ *ᵥ (fun x => W (x, y) ⟨a', (i', j')⟩) =
      if a' = a ∧ i'.1 = i.1 then (fun x => W (x, y) ⟨a', (i0', j')⟩) else 0 := by
  ext x
  change ∑ x', (A a i)ᴴ x x' * W (x', y) ⟨a', (i', j')⟩ = _
  rw [← kronecker_one_mul_apply, hA2 a i, mul_blockLeftOp_conjTranspose_apply,
    sum_star_leftUnit_eq W a a' i i' i0' hi0' j' (x, y)]
  split_ifs <;> rfl

lemma A_SR_ortho (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (A : ∀ a, Fin (dr a) → Matrix R R ℂ)
    (hA1 : ∀ a i, (A a i ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W =
      W * blockLeftOp (drb := drb) (leftUnit (dr := dr) a i))
    (hA2 : ∀ a i, ((A a i)ᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W =
      W * (blockLeftOp (drb := drb) (leftUnit (dr := dr) a i))ᴴ)
    (a a' : Fin N) (i : Fin (dr a)) (i' : Fin (dr a'))
    (u' : EuclideanSpace ℂ R) (hu' : u' ∈ SR W a') :
    (A a i)ᴴ *ᵥ (A a' i' *ᵥ u'.ofLp) =
      if a' = a ∧ i'.1 = i.1 then u'.ofLp else 0 := by
  induction hu' using Submodule.span_induction with
  | mem u' hu' =>
    rcases hu' with ⟨y, i0', j0', hi0', _, rfl⟩
    change (A a i)ᴴ *ᵥ (A a' i' *ᵥ (fun x => W (x, y) ⟨a', (i0', j0')⟩)) = _
    rw [A_mulVec_slice W A hA1 a' i' i0' hi0' j0' y,
      A_conjTranspose_mulVec_slice W A hA2 a a' i i' i0' hi0' j0' y]
    rfl
  | zero =>
    change (A a i)ᴴ *ᵥ (A a' i' *ᵥ (0 : R → ℂ)) = _
    simp
  | add x y _ _ hx hy =>
    change (A a i)ᴴ *ᵥ (A a' i' *ᵥ (x.ofLp + y.ofLp)) = _
    rw [mulVec_add, mulVec_add, hx, hy]
    split_ifs <;> simp
  | smul c x _ hx =>
    change (A a i)ᴴ *ᵥ (A a' i' *ᵥ (c • x.ofLp)) = _
    rw [mulVec_smul, mulVec_smul, hx]
    split_ifs <;> simp

lemma B_mulVec_slice (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (B : ∀ a, Fin (drb a) → Matrix Rb Rb ℂ)
    (hB1 : ∀ a j, ((1 : Matrix R R ℂ) ⊗ₖ B a j) * W =
      W * blockRightOp (dr := dr) (rightUnit (drb := drb) a j))
    (a : Fin N) (i : Fin (dr a)) (j j0 : Fin (drb a)) (hj0 : j0.1 = 0) (x : R) :
    B a j *ᵥ (fun y => W (x, y) ⟨a, (i, j0)⟩) = fun y => W (x, y) ⟨a, (i, j)⟩ := by
  ext y
  change ∑ y', B a j y y' * W (x, y') ⟨a, (i, j0)⟩ = _
  rw [← one_kronecker_mul_apply, hB1 a j, mul_blockRightOp_apply,
    sum_rightUnit_eq W a i j j0 hj0 (x, y)]

lemma B_conjTranspose_mulVec_slice (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (B : ∀ a, Fin (drb a) → Matrix Rb Rb ℂ)
    (hB2 : ∀ a j, ((1 : Matrix R R ℂ) ⊗ₖ (B a j)ᴴ) * W =
      W * (blockRightOp (dr := dr) (rightUnit (drb := drb) a j))ᴴ)
    (a a' : Fin N) (j : Fin (drb a)) (i' : Fin (dr a')) (j' j0' : Fin (drb a'))
    (hj0' : j0'.1 = 0) (x : R) :
    (B a j)ᴴ *ᵥ (fun y => W (x, y) ⟨a', (i', j')⟩) =
      if a' = a ∧ j'.1 = j.1 then (fun y => W (x, y) ⟨a', (i', j0')⟩) else 0 := by
  ext y
  change ∑ y', (B a j)ᴴ y y' * W (x, y') ⟨a', (i', j')⟩ = _
  rw [← one_kronecker_mul_apply, hB2 a j, mul_blockRightOp_conjTranspose_apply,
    sum_star_rightUnit_eq W a a' j i' j' j0' hj0' (x, y)]
  split_ifs <;> rfl

lemma B_SRb_ortho (W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ)
    (B : ∀ a, Fin (drb a) → Matrix Rb Rb ℂ)
    (hB1 : ∀ a j, ((1 : Matrix R R ℂ) ⊗ₖ B a j) * W =
      W * blockRightOp (dr := dr) (rightUnit (drb := drb) a j))
    (hB2 : ∀ a j, ((1 : Matrix R R ℂ) ⊗ₖ (B a j)ᴴ) * W =
      W * (blockRightOp (dr := dr) (rightUnit (drb := drb) a j))ᴴ)
    (a a' : Fin N) (j : Fin (drb a)) (j' : Fin (drb a'))
    (v' : EuclideanSpace ℂ Rb) (hv' : v' ∈ SRb W a') :
    (B a j)ᴴ *ᵥ (B a' j' *ᵥ v'.ofLp) =
      if a' = a ∧ j'.1 = j.1 then v'.ofLp else 0 := by
  induction hv' using Submodule.span_induction with
  | mem v' hv' =>
    rcases hv' with ⟨x, i0', j0', _, hj0', rfl⟩
    change (B a j)ᴴ *ᵥ (B a' j' *ᵥ (fun y => W (x, y) ⟨a', (i0', j0')⟩)) = _
    rw [B_mulVec_slice W B hB1 a' i0' j' j0' hj0' x,
      B_conjTranspose_mulVec_slice W B hB2 a a' j i0' j' j0' hj0' x]
    rfl
  | zero =>
    change (B a j)ᴴ *ᵥ (B a' j' *ᵥ (0 : Rb → ℂ)) = _
    simp
  | add x y _ _ hx hy =>
    change (B a j)ᴴ *ᵥ (B a' j' *ᵥ (x.ofLp + y.ofLp)) = _
    rw [mulVec_add, mulVec_add, hx, hy]
    split_ifs <;> simp
  | smul c x _ hx =>
    change (B a j)ᴴ *ᵥ (B a' j' *ᵥ (c • x.ofLp)) = _
    rw [mulVec_smul, mulVec_smul, hx]
    split_ifs <;> simp

lemma star_mulVec_dotProduct {I : Type} [Fintype I]
    (M : Matrix I I ℂ) (u v : I → ℂ) :
    ∑ x : I, star ((M *ᵥ u) x) * v x = ∑ x : I, star (u x) * (Mᴴ *ᵥ v) x := by
  simp only [mulVec, dotProduct, star_sum, star_mul', conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  ring

end MatrixLemmas

end HarlowTASI

open HarlowTASI

theorem solution {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V)
    (M : StarSubalgebra ℂ (Matrix C C ℂ))
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) (hMU : (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U)
    (h : ∀ O ∈ M, ∀ O' ∈ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)),
        ∃ (OR : Matrix R R ℂ) (ORb : Matrix Rb Rb ℂ),
          (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * O ∧
          (ORᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * Oᴴ ∧
          ((1 : Matrix R R ℂ) ⊗ₖ ORb) * V = V * O' ∧
          ((1 : Matrix R R ℂ) ⊗ₖ ORbᴴ) * V = V * O'ᴴ) :
    ∃ (m mb : Fin N → ℕ) (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
      (WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ)
      (WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ),
      IsIsometry WR ∧ IsIsometry WRb ∧ (∀ a, 0 < dr a → 0 < drb a → (χ a * (χ a)ᴴ).trace = 1) ∧
      ∀ (x : R) (y : Rb) (a : Fin N) (i : Fin (dr a)) (j : Fin (drb a)),
        (V * Uᴴ) (x, y) ⟨a, (i, j)⟩ =
          ∑ k, ∑ l, χ a k l * WR x ⟨a, (i, k)⟩ * WRb y ⟨a, (l, j)⟩ := by
  let W : Matrix (R × Rb) (BlockIndex N dr drb) ℂ := V * Uᴴ
  have hW_def : V * Uᴴ = W := rfl
  have hW : IsIsometry W := by
    unfold IsIsometry
    dsimp [W]
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul, hU.2]
  have hLeft : ∀ x : ∀ b, Matrix (Fin (dr b)) (Fin (dr b)) ℂ,
      ∃ OR : Matrix R R ℂ,
        (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W = W * blockLeftOp (drb := drb) x ∧
        (ORᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W = W * (blockLeftOp (drb := drb) x)ᴴ := by
    intro x
    have hxM : Uᴴ * blockLeftOp (drb := drb) x * U ∈ M := by
      rw [← SetLike.mem_coe, hMU]
      exact ⟨x, rfl⟩
    have h1M' : (1 : Matrix C C ℂ) ∈ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)) :=
      Subalgebra.one_mem _
    rcases h _ hxM 1 h1M' with ⟨OR, _, h1, h2, _, _⟩
    refine ⟨OR, ?_, ?_⟩
    · dsimp [W]
      rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, Matrix.mul_assoc, hU.2, Matrix.mul_one,
        ← Matrix.mul_assoc]
    · dsimp [W]
      rw [← Matrix.mul_assoc, h2]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [hU.2, Matrix.mul_one]
  have hRight : ∀ y : ∀ b, Matrix (Fin (drb b)) (Fin (drb b)) ℂ,
      ∃ ORb : Matrix Rb Rb ℂ,
        ((1 : Matrix R R ℂ) ⊗ₖ ORb) * W = W * blockRightOp (dr := dr) y ∧
        ((1 : Matrix R R ℂ) ⊗ₖ ORbᴴ) * W = W * (blockRightOp (dr := dr) y)ᴴ := by
    intro y
    have h1M : (1 : Matrix C C ℂ) ∈ M := Subalgebra.one_mem _
    have hyM' : Uᴴ * blockRightOp (dr := dr) y * U ∈
        StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)) := by
      have h_union : (M : Set (Matrix C C ℂ)) ∪ star (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U := by
        rw [Set.union_eq_left.mpr (fun a ha => by simpa using star_mem (s := M) ha), hMU]
      rw [← SetLike.mem_coe, StarSubalgebra.coe_centralizer, h_union, centralizer_blockAlgebraLeft U hU]
      exact ⟨y, rfl⟩
    rcases h 1 h1M _ hyM' with ⟨_, ORb, _, _, h3, h4⟩
    refine ⟨ORb, ?_, ?_⟩
    · dsimp [W]
      rw [← Matrix.mul_assoc, h3, Matrix.mul_assoc, Matrix.mul_assoc, hU.2, Matrix.mul_one,
        ← Matrix.mul_assoc]
    · dsimp [W]
      rw [← Matrix.mul_assoc, h4]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [hU.2, Matrix.mul_one]
  clear_value W
  let A : ∀ a, Fin (dr a) → Matrix R R ℂ :=
    fun a i => Classical.choose (hLeft (leftUnit (dr := dr) a i))
  have hA1 : ∀ a i, (A a i ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W =
      W * blockLeftOp (drb := drb) (leftUnit (dr := dr) a i) :=
    fun a i => (Classical.choose_spec (hLeft (leftUnit (dr := dr) a i))).1
  have hA2 : ∀ a i, ((A a i)ᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * W =
      W * (blockLeftOp (drb := drb) (leftUnit (dr := dr) a i))ᴴ :=
    fun a i => (Classical.choose_spec (hLeft (leftUnit (dr := dr) a i))).2
  let B : ∀ a, Fin (drb a) → Matrix Rb Rb ℂ :=
    fun a j => Classical.choose (hRight (rightUnit (drb := drb) a j))
  have hB1 : ∀ a j, ((1 : Matrix R R ℂ) ⊗ₖ B a j) * W =
      W * blockRightOp (dr := dr) (rightUnit (drb := drb) a j) :=
    fun a j => (Classical.choose_spec (hRight (rightUnit (drb := drb) a j))).1
  have hB2 : ∀ a j, ((1 : Matrix R R ℂ) ⊗ₖ (B a j)ᴴ) * W =
      W * (blockRightOp (dr := dr) (rightUnit (drb := drb) a j))ᴴ :=
    fun a j => (Classical.choose_spec (hRight (rightUnit (drb := drb) a j))).2
  let m : Fin N → ℕ := fun a => Module.finrank ℂ (SR W a)
  let mb : Fin N → ℕ := fun a => Module.finrank ℂ (SRb W a)
  let bR : ∀ a, OrthonormalBasis (Fin (m a)) ℂ (SR W a) :=
    fun a => stdOrthonormalBasis ℂ (SR W a)
  let bRb : ∀ a, OrthonormalBasis (Fin (mb a)) ℂ (SRb W a) :=
    fun a => stdOrthonormalBasis ℂ (SRb W a)
  let wR : ∀ a, Fin (m a) → R → ℂ :=
    fun a k => ((bR a k : SR W a) : EuclideanSpace ℂ R).ofLp
  let wRb : ∀ a, Fin (mb a) → Rb → ℂ :=
    fun a l => ((bRb a l : SRb W a) : EuclideanSpace ℂ Rb).ofLp
  let χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ :=
    fun a k l =>
      if h0 : 0 < dr a ∧ 0 < drb a then
        ∑ r : R, ∑ s : Rb, star (wR a k r) * star (wRb a l s) *
          W (r, s) ⟨a, (⟨0, h0.1⟩, ⟨0, h0.2⟩)⟩
      else 0
  let WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ :=
    fun r ⟨a, (i, k)⟩ => (A a i *ᵥ wR a k) r
  let WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ :=
    fun rb ⟨a, (l, j)⟩ => (B a j *ᵥ wRb a l) rb
  have hW_i0j0 : ∀ (a : Fin N) (hdr : 0 < dr a) (hdrb : 0 < drb a) (x' : R) (y' : Rb),
      W (x', y') ⟨a, (⟨0, hdr⟩, ⟨0, hdrb⟩)⟩ =
        ∑ k : Fin (m a), ∑ l : Fin (mb a), χ a k l * wR a k x' * wRb a l y' := by
    intro a hdr hdrb x' y'
    have hmemR : toE (fun r => W (r, y') ⟨a, (⟨0, hdr⟩, ⟨0, hdrb⟩)⟩) ∈ SR W a :=
      Submodule.subset_span ⟨y', ⟨0, hdr⟩, ⟨0, hdrb⟩, rfl, rfl, rfl⟩
    have hsumR := sub_onb_sum (SR W a) (fun r => W (r, y') ⟨a, (⟨0, hdr⟩, ⟨0, hdrb⟩)⟩) hmemR x'
    dsimp only [bR, wR, m] at hsumR ⊢
    rw [hsumR]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hmemRb : ∀ r : R, toE (fun s => W (r, s) ⟨a, (⟨0, hdr⟩, ⟨0, hdrb⟩)⟩) ∈ SRb W a :=
      fun r => Submodule.subset_span ⟨r, ⟨0, hdr⟩, ⟨0, hdrb⟩, rfl, rfl, rfl⟩
    have h_inner : (∑ r' : R, star (wR a k r') * W (r', y') ⟨a, (⟨0, hdr⟩, ⟨0, hdrb⟩)⟩) =
        ∑ l : Fin (mb a), χ a k l * wRb a l y' := by
      have h_expand : ∀ r' : R, W (r', y') ⟨a, (⟨0, hdr⟩, ⟨0, hdrb⟩)⟩ =
          ∑ l : Fin (mb a),
            (∑ s : Rb, star (wRb a l s) * W (r', s) ⟨a, (⟨0, hdr⟩, ⟨0, hdrb⟩)⟩) *
              wRb a l y' :=
        fun r' => sub_onb_sum (SRb W a) _ (hmemRb r') y'
      have h_lhs_eq : (∑ r' : R, star (wR a k r') * W (r', y') ⟨a, (⟨0, hdr⟩, ⟨0, hdrb⟩)⟩) =
          ∑ r' : R, ∑ l : Fin (mb a),
            star (wR a k r') * ((∑ s : Rb, star (wRb a l s) * W (r', s) ⟨a, (⟨0, hdr⟩, ⟨0, hdrb⟩)⟩) *
              wRb a l y') := by
        refine Finset.sum_congr rfl fun r' _ => ?_
        rw [h_expand r', Finset.mul_sum]
      rw [h_lhs_eq, Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      dsimp [χ]
      rw [dif_pos ⟨hdr, hdrb⟩]
      refine Eq.trans ?_ (Finset.sum_mul _ _ _).symm
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [← mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring
    rw [h_inner, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  refine ⟨m, mb, χ, WR, WRb, ?_, ?_, ?_, ?_⟩
  · -- IsIsometry WR
    unfold IsIsometry
    ext ⟨a, ⟨i, k⟩⟩ ⟨a', ⟨i', k'⟩⟩
    rw [mul_apply]
    change ∑ r : R, star ((A a i *ᵥ wR a k) r) * (A a' i' *ᵥ wR a' k') r = _
    rw [star_mulVec_dotProduct]
    have hk' : ((bR a' k' : SR W a') : EuclideanSpace ℂ R) ∈ SR W a' := (bR a' k').2
    rw [A_SR_ortho W A hA1 hA2 a a' i i' _ hk']
    rcases eq_or_ne a a' with rfl | ha
    · rcases eq_or_ne i i' with rfl | hi
      · rw [if_pos ⟨rfl, rfl⟩, sub_onb_ortho (SR W a) k k']
        rcases eq_or_ne k k' with rfl | hk
        · rw [if_pos rfl, one_apply_eq]
        · have hne : (⟨a, (i, k)⟩ : Σ b : Fin N, Fin (dr b) × Fin (m b)) ≠ ⟨a, (i, k')⟩ := by
            intro h_eq
            injection h_eq with _ h_pair
            injection h_pair with _ hk_eq
            exact hk hk_eq
          rw [if_neg hk, one_apply_ne hne]
      · have hne : (⟨a, (i, k)⟩ : Σ b : Fin N, Fin (dr b) × Fin (m b)) ≠ ⟨a, (i', k')⟩ := by
          intro h_eq
          injection h_eq with _ h_pair
          injection h_pair with hi_eq _
          exact hi hi_eq
        have hi_val : ¬(i'.1 = i.1) := fun h_val => hi (Fin.ext h_val.symm)
        rw [if_neg (fun h_and => hi_val h_and.2), one_apply_ne hne]
        simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    · have hne : (⟨a, (i, k)⟩ : Σ b : Fin N, Fin (dr b) × Fin (m b)) ≠ ⟨a', (i', k')⟩ := by
        intro h_eq
        injection h_eq with ha_eq _
        exact ha ha_eq
      rw [if_neg (fun h_and => ha h_and.1.symm), one_apply_ne hne]
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · -- IsIsometry WRb
    unfold IsIsometry
    ext ⟨a, ⟨l, j⟩⟩ ⟨a', ⟨l', j'⟩⟩
    rw [mul_apply]
    change ∑ rb : Rb, star ((B a j *ᵥ wRb a l) rb) * (B a' j' *ᵥ wRb a' l') rb = _
    rw [star_mulVec_dotProduct]
    have hl' : ((bRb a' l' : SRb W a') : EuclideanSpace ℂ Rb) ∈ SRb W a' := (bRb a' l').2
    rw [B_SRb_ortho W B hB1 hB2 a a' j j' _ hl']
    rcases eq_or_ne a a' with rfl | ha
    · rcases eq_or_ne j j' with rfl | hj
      · rw [if_pos ⟨rfl, rfl⟩, sub_onb_ortho (SRb W a) l l']
        rcases eq_or_ne l l' with rfl | hl
        · rw [if_pos rfl, one_apply_eq]
        · have hne : (⟨a, (l, j)⟩ : Σ b : Fin N, Fin (mb b) × Fin (drb b)) ≠ ⟨a, (l', j)⟩ := by
            intro h_eq
            injection h_eq with _ h_pair
            injection h_pair with hl_eq _
            exact hl hl_eq
          rw [if_neg hl, one_apply_ne hne]
      · have hne : (⟨a, (l, j)⟩ : Σ b : Fin N, Fin (mb b) × Fin (drb b)) ≠ ⟨a, (l', j')⟩ := by
          intro h_eq
          injection h_eq with _ h_pair
          injection h_pair with _ hj_eq
          exact hj hj_eq
        have hj_val : ¬(j'.1 = j.1) := fun h_val => hj (Fin.ext h_val.symm)
        rw [if_neg (fun h_and => hj_val h_and.2), one_apply_ne hne]
        simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    · have hne : (⟨a, (l, j)⟩ : Σ b : Fin N, Fin (mb b) × Fin (drb b)) ≠ ⟨a', (l', j')⟩ := by
        intro h_eq
        injection h_eq with ha_eq _
        exact ha ha_eq
      rw [if_neg (fun h_and => ha h_and.1.symm), one_apply_ne hne]
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · -- Trace normalization of χ a
    intro a hdr hdrb
    let i0 : Fin (dr a) := ⟨0, hdr⟩
    let j0 : Fin (drb a) := ⟨0, hdrb⟩
    have hnorm : ∑ x : R, ∑ y : Rb,
        star (W (x, y) ⟨a, (i0, j0)⟩) * W (x, y) ⟨a, (i0, j0)⟩ = 1 := by
      have h1 := congr_fun (congr_fun hW ⟨a, (i0, j0)⟩) ⟨a, (i0, j0)⟩
      rw [mul_apply, Fintype.sum_prod_type, one_apply_eq] at h1
      exact h1
    rw [← hnorm]
    simp only [trace, diag_apply, mul_apply]
    have h_lhs : (∑ k : Fin (m a), ∑ l : Fin (mb a), χ a k l * (χ a)ᴴ l k) =
        ∑ k : Fin (m a), ∑ l : Fin (mb a),
          χ a k l * (∑ x : R, ∑ y : Rb,
            star (W (x, y) ⟨a, (i0, j0)⟩) * wR a k x * wRb a l y) := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      congr 1
      change star (if h0 : 0 < dr a ∧ 0 < drb a then
          ∑ r : R, ∑ s : Rb, star (wR a k r) * star (wRb a l s) *
            W (r, s) ⟨a, (⟨0, h0.1⟩, ⟨0, h0.2⟩)⟩
        else 0) = _
      rw [dif_pos ⟨hdr, hdrb⟩, star_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [star_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [star_mul', star_mul', star_star, star_star]
      change wR a k x * wRb a l y * star (W (x, y) ⟨a, (i0, j0)⟩) = _
      ring
    rw [h_lhs]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun l _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h_rhs_term : star (W (x, y) ⟨a, (i0, j0)⟩) * W (x, y) ⟨a, (i0, j0)⟩ =
        star (W (x, y) ⟨a, (i0, j0)⟩) *
          (∑ k : Fin (m a), ∑ l : Fin (mb a), χ a k l * wR a k x * wRb a l y) :=
      congr_arg (star (W (x, y) ⟨a, (i0, j0)⟩) * ·) (hW_i0j0 a hdr hdrb x y)
    rw [h_rhs_term]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  · -- Factorization of (V * Uᴴ) (x, y) ⟨a, (i, j)⟩
    intro x y a i j
    rw [hW_def]
    have hdr : 0 < dr a := Nat.zero_lt_of_lt i.2
    have hdrb : 0 < drb a := Nat.zero_lt_of_lt j.2
    let i0 : Fin (dr a) := ⟨0, hdr⟩
    let j0 : Fin (drb a) := ⟨0, hdrb⟩
    have hA_step := congr_fun (A_mulVec_slice W A hA1 a i i0 rfl j y) x
    change (A a i *ᵥ fun x' => W (x', y) ⟨a, (i0, j)⟩) x = W (x, y) ⟨a, (i, j)⟩ at hA_step
    rw [← hA_step]
    change ∑ x' : R, A a i x x' * W (x', y) ⟨a, (i0, j)⟩ = _
    have hB_step : ∀ x' : R, W (x', y) ⟨a, (i0, j)⟩ =
        ∑ y' : Rb, B a j y y' * W (x', y') ⟨a, (i0, j0)⟩ := by
      intro x'
      have h := congr_fun (B_mulVec_slice W B hB1 a i0 j j0 rfl x') y
      exact h.symm
    have h_step1 : (∑ x' : R, A a i x x' * W (x', y) ⟨a, (i0, j)⟩) =
        ∑ x' : R, ∑ y' : Rb, ∑ k : Fin (m a), ∑ l : Fin (mb a),
          A a i x x' * (B a j y y' * (χ a k l * wR a k x' * wRb a l y')) := by
      refine Finset.sum_congr rfl fun x' _ => ?_
      rw [hB_step x', Finset.mul_sum]
      refine Finset.sum_congr rfl fun y' _ => ?_
      rw [hW_i0j0 a hdr hdrb x' y', Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [h_step1]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun y' _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun x' _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    dsimp [WR, WRb, mulVec, dotProduct]
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ => ?_
    ring
