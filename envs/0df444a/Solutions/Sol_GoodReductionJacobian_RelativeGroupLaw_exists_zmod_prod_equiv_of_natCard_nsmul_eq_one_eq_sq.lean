-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_zmod_prod_equiv_of_natCard_nsmul_eq_one_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/9a276be8-f0ff-597c-a213-a18a92fa7fb5

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_zmod_prod_equiv_of_natCard_nsmul_eq_one_eq_sq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace L1fAux

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

theorem pow_eq_nsmul (P : SchemeHomOver t f) (n : ℕ) :
    (letI := L.pointGroup t; P ^ n) = L.nsmul t n P := by
  letI := L.pointGroup t
  induction n with
  | zero => rw [pow_zero, RelativeGroupLaw.nsmul_zero]; rfl
  | succ n ih => rw [pow_succ, ih, RelativeGroupLaw.nsmul_succ]; rfl

end L1fAux

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (H : Set (SchemeHomOver t f)) (hfin : H.Finite)
    (hone : L.one t ∈ H) (hmul : ∀ P Q : SchemeHomOver t f, P ∈ H → Q ∈ H → L.mul t P Q ∈ H)
    (hinv : ∀ P : SchemeHomOver t f, P ∈ H → L.inv t P ∈ H)
    (N : ℕ) [NeZero N] (hN : ∀ P : SchemeHomOver t f, P ∈ H → L.nsmul t N P = L.one t)
    (hcard : ∀ d : ℕ, d ∣ N → Nat.card {P : ↥H // L.nsmul t d P.1 = L.one t} = d ^ 2) :
    ∃ e : ZMod N × ZMod N ≃ ↥H,
      ∀ x y : ZMod N × ZMod N, (e (x + y) : SchemeHomOver t f) = L.mul t (e x) (e y) := by
  classical
  letI grp : Group (SchemeHomOver t f) := L.pointGroup t
  let H' : Subgroup (SchemeHomOver t f) :=
    { carrier := H, mul_mem' := fun {P Q} hP hQ => hmul P Q hP hQ, one_mem' := hone, inv_mem' := fun {P} hP => hinv P hP }
  letI : CommGroup ↥H' := { (inferInstance : Group ↥H') with mul_comm := fun x y => Subtype.ext (hc t x.1 y.1) }
  let M := Additive ↥H'

  have hpow : ∀ (x : ↥H') (n : ℕ), ((x ^ n : ↥H') : SchemeHomOver t f) = L.nsmul t n x.1 := by
    intro x n
    rw [Subgroup.coe_pow]
    exact L1fAux.pow_eq_nsmul L t x.1 n

  have hmem : ∀ (d : ℕ) (x : M), x ∈ Submodule.torsionBy ℤ M d ↔ L.nsmul t d (Additive.toMul x).1 = L.one t := by
    intro d x
    rw [Submodule.mem_torsionBy_iff]
    change ((d : ℕ) : ℤ) • x = 0 ↔ _
    rw [natCast_zsmul]
    constructor
    · intro h
      have h1 : (Additive.toMul x) ^ d = 1 := by
        rw [← toMul_nsmul, h]; rfl
      have h2 := congrArg (fun y : ↥H' => (y : SchemeHomOver t f)) h1
      rw [← hpow]; exact h2
    · intro h
      have h1 : (Additive.toMul x) ^ d = 1 := by
        apply Subtype.ext
        rw [hpow]
        exact h
      rw [← ofMul_toMul x, ← ofMul_pow, h1, ofMul_one]

  have hcard' : ∀ d : ℕ, d ∣ N → Nat.card (Submodule.torsionBy ℤ M d) = d ^ 2 := by
    intro d hd
    rw [← hcard d hd]
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨(Additive.toMul x.1).1, (Additive.toMul x.1).2⟩, (hmem d x.1).mp x.2⟩
        invFun := fun P => ⟨Additive.ofMul ⟨P.1.1, P.1.2⟩, (hmem d _).mpr P.2⟩
        left_inv := fun x => rfl
        right_inv := fun P => rfl }
  obtain ⟨e₀⟩ := AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq (A := M) (NeZero.ne N) hcard'

  have hall : ∀ P : ↥H, (Additive.ofMul (⟨P.1, P.2⟩ : ↥H') : M) ∈ Submodule.torsionBy ℤ M N :=
    fun P => (hmem N _).mpr (hN P.1 P.2)
  let e : ZMod N × ZMod N ≃ ↥H :=
    { toFun := fun x => ⟨(Additive.toMul (e₀ x).1).1, (Additive.toMul (e₀ x).1).2⟩
      invFun := fun P => e₀.symm ⟨Additive.ofMul ⟨P.1, P.2⟩, hall P⟩
      left_inv := fun x => by
        change e₀.symm ⟨(e₀ x).1, _⟩ = x
        rw [Subtype.coe_eta, AddEquiv.symm_apply_apply]
      right_inv := fun P => by
        apply Subtype.ext
        change (Additive.toMul (e₀ (e₀.symm ⟨Additive.ofMul ⟨P.1, P.2⟩, hall P⟩)).1).1 = P.1
        rw [AddEquiv.apply_symm_apply]
        rfl }
  refine ⟨e, fun x y => ?_⟩
  change (Additive.toMul (e₀ (x + y)).1).1 = L.mul t (Additive.toMul (e₀ x).1).1 (Additive.toMul (e₀ y).1).1
  rw [map_add]
  rfl

end S_GoodReductionJacobian_RelativeGroupLaw_exists_zmod_prod_equiv_of_natCard_nsmul_eq_one_eq_sq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_zmod_prod_equiv_of_natCard_nsmul_eq_one_eq_sq (solution)
