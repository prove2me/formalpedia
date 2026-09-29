-- Prove2me | solution 1 for Matrix.exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/45ac4455-addc-5efb-9a89-e467aa5905ac

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe

set_option autoImplicit false

universe u

namespace R4E1Ord

open Matrix

variable {p : ℕ} [hp : Fact p.Prime]

section FreeModule

variable {V : Type*} [AddCommGroup V] [Module ℤ_[p] V] [Module.Free ℤ_[p] V] [Module.Finite ℤ_[p] V]

theorem eq_zero_of_forall_mem_span_pow {x : ℤ_[p]}
    (hx : ∀ N : ℕ, x ∈ (Ideal.span {(p : ℤ_[p]) ^ N} : Ideal ℤ_[p])) : x = 0 := by
  by_contra h
  have := (PadicInt.mem_span_pow_iff_le_valuation x h (x.valuation + 1)).1 (hx _)
  omega

theorem exists_pow_smul_mem_range_of_injective (f : V →ₗ[ℤ_[p]] V) (hf : Function.Injective f) :
    ∃ m' : ℕ, ∀ w : V, ∃ v : V, f v = (p : ℤ_[p]) ^ m' • w := by
  classical
  let b := Module.Free.chooseBasis ℤ_[p] V
  let G : Matrix _ _ ℤ_[p] := LinearMap.toMatrix b b f

  have hdet : G.det ≠ 0 := by
    intro hG
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hG

    let x : V := b.equivFun.symm c
    have hxrepr : ⇑(b.repr x) = c := by
      have : b.equivFun x = c := b.equivFun.apply_symm_apply c
      rw [Module.Basis.equivFun_apply] at this
      exact this
    have hfx : f x = 0 := by
      have h := LinearMap.toMatrix_mulVec_repr b b f x
      rw [hxrepr] at h
      change G.mulVec c = ⇑(b.repr (f x)) at h
      rw [hc] at h
      have h' : b.repr (f x) = 0 := by
        ext i
        have := congrFun h i
        simpa using this.symm
      exact b.repr.map_eq_zero_iff.mp h'
    have hx0 : x = 0 := hf (by rw [hfx, map_zero])
    apply hc0
    rw [← hxrepr, hx0, map_zero]
    rfl

  refine ⟨G.det.valuation, fun w => ?_⟩
  set m' := G.det.valuation
  have hspec : G.det = (PadicInt.unitCoeff hdet : ℤ_[p]) * (p : ℤ_[p]) ^ m' := PadicInt.unitCoeff_spec hdet
  set u : ℤ_[p]ˣ := PadicInt.unitCoeff hdet

  let cw : _ → ℤ_[p] := ⇑(b.repr w)
  let v' : _ → ℤ_[p] := (↑u⁻¹ : ℤ_[p]) • (G.adjugate.mulVec cw)
  have hGv' : G.mulVec v' = (p : ℤ_[p]) ^ m' • cw := by
    simp only [v']
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec G.det,
      Matrix.one_mulVec, smul_smul, hspec, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨b.equivFun.symm v', ?_⟩
  apply b.repr.injective
  have hrepr : ⇑(b.repr (b.equivFun.symm v')) = v' := by
    have : b.equivFun (b.equivFun.symm v') = v' := b.equivFun.apply_symm_apply v'
    rwa [Module.Basis.equivFun_apply] at this
  have h := LinearMap.toMatrix_mulVec_repr b b f (b.equivFun.symm v')
  rw [hrepr] at h
  change G.mulVec v' = ⇑(b.repr (f (b.equivFun.symm v'))) at h
  rw [hGv'] at h
  ext i
  have := congrFun h i
  rw [← this, map_smul]
  rfl

end FreeModule

section Transport

variable {A : Type u} [Ring A] {n : Type} [Fintype n] [DecidableEq n]

noncomputable abbrev up : Matrix n n ℤ_[p] →+* Matrix n n ℚ_[p] := (algebraMap ℤ_[p] ℚ_[p]).mapMatrix

theorem up_apply (M : Matrix n n ℤ_[p]) : up M = M.map ((↑) : ℤ_[p] → ℚ_[p]) := rfl

theorem up_injective : Function.Injective (up : Matrix n n ℤ_[p] → Matrix n n ℚ_[p]) := fun M N h => by
  ext i j
  have := congrFun (congrFun h i) j
  exact Subtype.ext this

theorem up_smul (z : ℤ_[p]) (M : Matrix n n ℤ_[p]) : up (z • M) = (z : ℚ_[p]) • up M := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

theorem up_pow_smul (k : ℕ) (M : Matrix n n ℤ_[p]) :
    up ((p : ℤ_[p]) ^ k • M) = (p : ℚ_[p]) ^ k • up M := by
  rw [up_smul]; push_cast; rfl

omit [Fintype n] [DecidableEq n] in
theorem natCast_pow_smul_eq (k : ℕ) (Y : Matrix n n ℚ_[p]) :
    (p ^ k : ℕ) • Y = (p : ℚ_[p]) ^ k • Y := by
  rw [← Nat.cast_smul_eq_nsmul ℚ_[p], Nat.cast_pow]

omit [Fintype n] [DecidableEq n] in
theorem natCast_pow_smul_eq' (k : ℕ) (Y : Matrix n n ℤ_[p]) :
    (p ^ k : ℕ) • Y = (p : ℤ_[p]) ^ k • Y := by
  rw [← Nat.cast_smul_eq_nsmul ℤ_[p], Nat.cast_pow]

variable (θ E : A →+* Matrix n n ℚ_[p]) (hθ : Function.Injective θ) (hE : Function.Injective E) (m : ℕ)
  (hθm : ∀ M : Matrix n n ℤ_[p], ∃ a : A, θ a = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p]))
  (hEint : ∀ a : A, ∃ M : Matrix n n ℤ_[p], E a = M.map ((↑) : ℤ_[p] → ℚ_[p]))

noncomputable def aOf (M : Matrix n n ℤ_[p]) : A := (hθm M).choose

theorem θ_aOf (M : Matrix n n ℤ_[p]) : θ (aOf θ m hθm M) = (p : ℚ_[p]) ^ m • up M :=
  (hθm M).choose_spec

include hθ in
theorem aOf_add (M N : Matrix n n ℤ_[p]) : aOf θ m hθm (M + N) = aOf θ m hθm M + aOf θ m hθm N :=
  hθ (by rw [map_add, θ_aOf, θ_aOf, θ_aOf, map_add, smul_add])

include hθ in
theorem aOf_mul (M N : Matrix n n ℤ_[p]) :
    aOf θ m hθm M * aOf θ m hθm N = (p ^ m : ℕ) • aOf θ m hθm (M * N) :=
  hθ (by
    rw [map_mul, θ_aOf, θ_aOf, map_nsmul, θ_aOf, natCast_pow_smul_eq, map_mul, smul_mul_smul_comm,
      smul_smul])

include hθ in
theorem aOf_one : aOf θ m hθm 1 = (p ^ m : ℕ) • (1 : A) :=
  hθ (by rw [θ_aOf, map_nsmul, map_one, natCast_pow_smul_eq, map_one])

include hθ in
theorem aOf_nsmul (k : ℕ) (M : Matrix n n ℤ_[p]) : aOf θ m hθm (k • M) = k • aOf θ m hθm M :=
  hθ (by rw [θ_aOf, map_nsmul, map_nsmul, θ_aOf, smul_comm])

noncomputable def FOf (M : Matrix n n ℤ_[p]) : Matrix n n ℤ_[p] := (hEint (aOf θ m hθm M)).choose

theorem up_FOf (M : Matrix n n ℤ_[p]) : up (FOf θ E m hθm hEint M) = E (aOf θ m hθm M) :=
  ((hEint (aOf θ m hθm M)).choose_spec).symm

include hθ in
theorem FOf_add (M N : Matrix n n ℤ_[p]) :
    FOf θ E m hθm hEint (M + N) = FOf θ E m hθm hEint M + FOf θ E m hθm hEint N :=
  up_injective (by rw [map_add, up_FOf, up_FOf, up_FOf, aOf_add θ hθ, map_add])

include hθ in
theorem FOf_mul (M N : Matrix n n ℤ_[p]) :
    FOf θ E m hθm hEint M * FOf θ E m hθm hEint N = (p : ℤ_[p]) ^ m • FOf θ E m hθm hEint (M * N) :=
  up_injective (by
    rw [map_mul, up_FOf, up_FOf, up_pow_smul, up_FOf, ← map_mul, aOf_mul θ hθ, map_nsmul,
      natCast_pow_smul_eq])

include hθ in
theorem FOf_one : FOf θ E m hθm hEint 1 = (p : ℤ_[p]) ^ m • (1 : Matrix n n ℤ_[p]) :=
  up_injective (by rw [up_FOf, aOf_one θ hθ, map_nsmul, map_one, up_pow_smul, map_one, natCast_pow_smul_eq])

include hθ in
theorem FOf_nsmul (k : ℕ) (M : Matrix n n ℤ_[p]) :
    FOf θ E m hθm hEint (k • M) = k • FOf θ E m hθm hEint M :=
  up_injective (by rw [up_FOf, aOf_nsmul θ hθ, map_nsmul, map_nsmul, up_FOf])

include hE in
theorem FOf_injective {M : Matrix n n ℤ_[p]} (h : FOf θ E m hθm hEint M = 0) : M = 0 := by
  have h1 : E (aOf θ m hθm M) = 0 := by rw [← up_FOf θ E m hθm hEint, h, map_zero]
  have h2 : aOf θ m hθm M = 0 := hE (by rw [h1, map_zero])
  have h3 : θ (aOf θ m hθm M) = 0 := by rw [h2, map_zero]
  rw [θ_aOf] at h3
  have h4 : up M = 0 := by
    have hp : (p : ℚ_[p]) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
    exact (smul_eq_zero.mp h3).resolve_left hp
  exact up_injective (by rw [h4, map_zero])

noncomputable def DOf (z : ℤ_[p]) : Matrix n n ℤ_[p] :=
  FOf θ E m hθm hEint (z • (1 : Matrix n n ℤ_[p])) - ((p : ℤ_[p]) ^ m * z) • (1 : Matrix n n ℤ_[p])

include hθ in
theorem DOf_natCast (k : ℕ) : DOf θ E m hθm hEint (k : ℤ_[p]) = 0 := by
  rw [DOf, Nat.cast_smul_eq_nsmul, FOf_nsmul θ E hθ, FOf_one θ E hθ, ← Nat.cast_smul_eq_nsmul ℤ_[p],
    smul_smul, mul_comm, sub_self]

include hθ in
theorem DOf_add (z z' : ℤ_[p]) :
    DOf θ E m hθm hEint (z + z') = DOf θ E m hθm hEint z + DOf θ E m hθm hEint z' := by
  simp only [DOf]
  rw [add_smul, FOf_add θ E hθ, mul_add, add_smul]
  abel

include hθ in
theorem DOf_pow_mul (N : ℕ) (y : ℤ_[p]) :
    DOf θ E m hθm hEint ((p : ℤ_[p]) ^ N * y) = (p : ℤ_[p]) ^ N • DOf θ E m hθm hEint y := by
  simp only [DOf]
  rw [mul_smul, ← natCast_pow_smul_eq', FOf_nsmul θ E hθ, natCast_pow_smul_eq', smul_sub, smul_smul]
  congr 2
  ring

include hθ in

theorem DOf_eq_zero (z : ℤ_[p]) : DOf θ E m hθm hEint z = 0 := by
  ext i j
  apply eq_zero_of_forall_mem_span_pow
  intro N

  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec N z)
  have hz : z = (z.appr N : ℤ_[p]) + (p : ℤ_[p]) ^ N * y := by rw [mul_comm, hy]; ring
  rw [hz, DOf_add θ E hθ, DOf_natCast θ E hθ, zero_add, DOf_pow_mul θ E hθ, Matrix.smul_apply,
    smul_eq_mul, mul_comm]
  exact Ideal.mem_span_singleton'.2 ⟨_, rfl⟩

include hθ in
theorem FOf_smul_one (z : ℤ_[p]) :
    FOf θ E m hθm hEint (z • (1 : Matrix n n ℤ_[p])) = ((p : ℤ_[p]) ^ m * z) • (1 : Matrix n n ℤ_[p]) := by
  have h := DOf_eq_zero θ E hθ m hθm hEint z
  rwa [DOf, sub_eq_zero] at h

include hθ in

theorem FOf_smul (z : ℤ_[p]) (M : Matrix n n ℤ_[p]) :
    FOf θ E m hθm hEint (z • M) = z • FOf θ E m hθm hEint M := by
  have h := FOf_mul θ E hθ m hθm hEint (z • (1 : Matrix n n ℤ_[p])) M
  rw [FOf_smul_one θ E hθ, smul_one_mul, Matrix.smul_mul, Matrix.one_mul, mul_smul] at h
  have hp : (p : ℤ_[p]) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  exact (smul_right_injective (Matrix n n ℤ_[p]) hp h).symm

noncomputable def FLin : Matrix n n ℤ_[p] →ₗ[ℤ_[p]] Matrix n n ℤ_[p] where
  toFun := FOf θ E m hθm hEint
  map_add' := FOf_add θ E hθ m hθm hEint
  map_smul' := FOf_smul θ E hθ m hθm hEint

include hE in
theorem FLin_injective : Function.Injective (FLin θ E hθ m hθm hEint) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro M hM
  exact FOf_injective θ E hE m hθm hEint hM

include hθ hE hθm hEint in
theorem main :
    ∃ m' : ℕ, ∀ M : Matrix n n ℤ_[p], ∃ a : A, E a = (p : ℚ_[p]) ^ m' • M.map ((↑) : ℤ_[p] → ℚ_[p]) := by
  obtain ⟨m', hm'⟩ := exists_pow_smul_mem_range_of_injective (FLin θ E hθ m hθm hEint)
    (FLin_injective θ E hθ hE m hθm hEint)
  refine ⟨m', fun M => ?_⟩
  obtain ⟨M', hM'⟩ := hm' M
  refine ⟨aOf θ m hθm M', ?_⟩
  change FOf θ E m hθm hEint M' = (p : ℤ_[p]) ^ m' • M at hM'
  rw [← up_FOf θ E m hθm hEint, hM', up_pow_smul]
  rfl

end Transport

end R4E1Ord

theorem solution
    (p : ℕ) [Fact p.Prime] {A : Type u} [Ring A] {n : Type} [Fintype n] [DecidableEq n]
    (θ E : A →+* Matrix n n ℚ_[p]) (hθ : Function.Injective θ) (hE : Function.Injective E) (m : ℕ)
    (hθm : ∀ M : Matrix n n ℤ_[p], ∃ a : A, θ a = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p]))
    (hEint : ∀ a : A, ∃ M : Matrix n n ℤ_[p], E a = M.map ((↑) : ℤ_[p] → ℚ_[p])) :
    ∃ m' : ℕ, ∀ M : Matrix n n ℤ_[p], ∃ a : A, E a = (p : ℚ_[p]) ^ m' • M.map ((↑) : ℤ_[p] → ℚ_[p]) :=
  R4E1Ord.main θ E hθ hE m hθm hEint

end S_Matrix_exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe
end P2MW
export P2MW.S_Matrix_exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe (solution)
