-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-14T08:28:30.534893+00:00
-- url     : https://prove2.me/submissions/020d8b28-3075-4d55-9a63-3df120ba546f

import Mathlib
import Definitions.Def_BooneHigman_Steinberg
import Definitions.Def_BooneHigman_cornerSub
import Definitions.Def_OAI_FiniteAlgebraicEnvelopes_steinCoeffMap
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_4_4
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_4_5

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

variable {n : ℕ} {R : Type u} [Ring R]

theorem steinLam_add (psi : R → R) (hpsi_add : ∀ a b : R, psi (a + b) = psi a + psi b) (Q : R)
    (a b : R) : psi (a + b) * Q = psi a * Q + psi b * Q := by
  rw [hpsi_add, add_mul]

theorem steinLam_mul (psi : R → R) (hpsi_mul : ∀ a b : R, psi (a * b) = psi a * psi b) (Q : R)
    (hQpsi : ∀ a : R, Q * psi a = psi a * Q) (hQQ : Q * Q = Q) (a b : R) :
    psi (a * b) * Q = (psi a * Q) * (psi b * Q) := by
  rw [hpsi_mul, show (psi a * Q) * (psi b * Q) = psi a * (Q * psi b) * Q from by noncomm_ring,
    hQpsi b, show psi a * (psi b * Q) * Q = psi a * psi b * (Q * Q) from by noncomm_ring, hQQ]
theorem steinCoeffMap_corner_gen (psi : R → R) (E : R) (hE : E * E = E)
    (hcomm : ∀ a : R, E * psi a = psi a * E) (i j : Fin n) (hij : i ≠ j) (a : R) :
    SteinbergGroup.x i j hij (psi a * E) ∈ cornerSub E := by
  have heq : psi a * E = E * (psi a) * E := by rw [hcomm a, mul_assoc, hE]
  rw [heq]
  exact Subgroup.subset_closure ⟨i, j, hij, psi a, rfl⟩

/-- `steinCoeffMap` for `λ(a) = ψ(a)E` sends EVERY element of `St_n(R)` into `cornerSub E`
(not just the generators), provided `E` is idempotent and commutes with `ψ(R)`. -/
theorem steinCoeffMap_mem_cornerSub (psi : R → R) (E : R) (hE : E * E = E)
    (hcomm : ∀ a : R, E * psi a = psi a * E)
    (hadd : ∀ a b : R, psi (a + b) * E = psi a * E + psi b * E)
    (hmul : ∀ a b : R, psi (a * b) * E = (psi a * E) * (psi b * E))
    (z : SteinbergGroup n R) :
    steinCoeffMap (fun a => psi a * E) hadd hmul z ∈ cornerSub E := by
  have hmem : z ∈ Subgroup.comap (steinCoeffMap (fun a => psi a * E) hadd hmul) (cornerSub E) := by
    apply PresentedGroup.generated_by (steinRelations n R)
    intro w
    show steinCoeffMap (fun a => psi a * E) hadd hmul
      (SteinbergGroup.x w.i w.j w.hij w.a) ∈ cornerSub E
    rw [steinCoeffMap_x]
    exact steinCoeffMap_corner_gen psi E hE hcomm w.i w.j w.hij w.a
  exact Subgroup.mem_comap.mp hmem
section OrthogonalSum

variable {Q1 Q2 : R} (hQ1Q1 : Q1 * Q1 = Q1) (hQ2Q2 : Q2 * Q2 = Q2) (hQ1Q2 : Q1 * Q2 = 0)
  (hQ2Q1 : Q2 * Q1 = 0) (psi : R → R) (hQ1psi : ∀ a : R, Q1 * psi a = psi a * Q1)
  (hQ2psi : ∀ a : R, Q2 * psi a = psi a * Q2)
  (hadd1 : ∀ a b : R, psi (a + b) * Q1 = psi a * Q1 + psi b * Q1)
  (hmul1 : ∀ a b : R, psi (a * b) * Q1 = (psi a * Q1) * (psi b * Q1))
  (hadd2 : ∀ a b : R, psi (a + b) * Q2 = psi a * Q2 + psi b * Q2)
  (hmul2 : ∀ a b : R, psi (a * b) * Q2 = (psi a * Q2) * (psi b * Q2))
  (haddQ : ∀ a b : R, psi (a + b) * (Q1 + Q2) = psi a * (Q1 + Q2) + psi b * (Q1 + Q2))
  (hmulQ : ∀ a b : R, psi (a * b) * (Q1 + Q2) = (psi a * (Q1 + Q2)) * (psi b * (Q1 + Q2)))
  (hex : ∀ i j : Fin n, i ≠ j → ∃ k0 : Fin n, k0 ≠ i ∧ k0 ≠ j)

include hQ1Q1 hQ2Q2 hQ1Q2 hQ2Q1 hQ1psi hQ2psi hex in
/-- `θ₁(z)` and `θ₂(w)` always commute, for `z, w` arbitrary (not just generators), since
both land in their respective corners and `lemma_4_5` covers the whole corner subgroups. -/
theorem steinCoeffMap_orthogonal_commute (z w : SteinbergGroup n R) :
    steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 z *
        steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 w =
      steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 w *
        steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 z :=
  lemma_4_5 (E := Q1) (F := Q2) hQ1Q2 hQ2Q1 hQ1Q1 hex _
    (steinCoeffMap_mem_cornerSub psi Q1 hQ1Q1 hQ1psi hadd1 hmul1 z) _
    (steinCoeffMap_mem_cornerSub psi Q2 hQ2Q2 hQ2psi hadd2 hmul2 w)

include hQ1Q1 hQ2Q2 hQ1Q2 hQ2Q1 hQ1psi hQ2psi hex in
/-- The orthogonal-sum MonoidHom `z ↦ θ₁(z)θ₂(z)`, well-defined (multiplicative) because
the two factors always commute. -/
noncomputable def steinCoeffMapSum : SteinbergGroup n R →* SteinbergGroup n R where
  toFun z := steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 z *
    steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 z
  map_one' := by
    show steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 1 *
      steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' z w := by
    show steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 (z * w) *
        steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 (z * w) =
      steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 z *
        steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 z *
        (steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 w *
          steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 w)
    have hcomm := steinCoeffMap_orthogonal_commute hQ1Q1 hQ2Q2 hQ1Q2 hQ2Q1 psi hQ1psi hQ2psi hadd1 hmul1 hadd2 hmul2
      hex w z
    calc steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 (z * w) *
        steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 (z * w)
        = (steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 z *
            steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 w) *
          (steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 z *
            steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 w) := by rw [map_mul, map_mul]
      _ = steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 z *
            (steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 w *
              steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 z) *
          steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 w := by group
      _ = steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 z *
            (steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 z *
              steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 w) *
          steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 w := by rw [hcomm]
      _ = steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 z *
            steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 z *
          (steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 w *
            steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 w) := by group

include hQ1Q1 hQ2Q2 hQ1Q2 hQ2Q1 hQ1psi hQ2psi hex in
/-- Equation (22)-(23)'s key tool: the coefficient map for an orthogonal SUM of idempotents
decomposes as the product of the two summands' coefficient maps. -/
theorem steinCoeffMap_orthogonal_sum (z : SteinbergGroup n R) :
    steinCoeffMap (fun a => psi a * (Q1 + Q2)) haddQ hmulQ z =
      steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 z *
        steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 z := by
  have hagree : steinCoeffMap (fun a => psi a * (Q1 + Q2)) haddQ hmulQ =
      steinCoeffMapSum hQ1Q1 hQ2Q2 hQ1Q2 hQ2Q1 psi hQ1psi hQ2psi hadd1 hmul1 hadd2 hmul2 hex :=
    PresentedGroup.ext (rels := steinRelations n R) (fun w => by
      show steinCoeffMap (fun a => psi a * (Q1 + Q2)) haddQ hmulQ
          (SteinbergGroup.x w.i w.j w.hij w.a) =
        steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 (SteinbergGroup.x w.i w.j w.hij w.a) *
          steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 (SteinbergGroup.x w.i w.j w.hij w.a)
      rw [steinCoeffMap_x, steinCoeffMap_x, steinCoeffMap_x,
        show psi w.a * (Q1 + Q2) = psi w.a * Q1 + psi w.a * Q2 from by noncomm_ring,
        steinberg_x_add])
  rw [hagree]
  rfl

end OrthogonalSum

/-- The sum of two orthogonal idempotents is idempotent — pure ring algebra, no corner
structure needed. -/
theorem orthogonal_idem_sum {a b : R} (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0)
    (hba : b * a = 0) : (a + b) * (a + b) = a + b := by
  calc (a + b) * (a + b) = a * a + a * b + b * a + b * b := by noncomm_ring
    _ = a + 0 + 0 + b := by rw [ha, hab, hba, hb]
    _ = a + b := by abel

/-! ### Theorem 4.1's own setup: `P, U0, U1, V0, V1` and the four corners `E0, E1, E00, E01`. -/
section Theorem41Setup

variable {P U0 U1 V0 V1 : R} (hP : P = P * P) (hU0 : U0 = P * U0 * P) (hU1 : U1 = P * U1 * P)
  (hV0 : V0 = P * V0 * P) (hV1 : V1 = P * V1 * P)
  (hV0U0 : V0 * U0 = P) (hV1U1 : V1 * U1 = P) (hV0U1 : V0 * U1 = 0) (hV1U0 : V1 * U0 = 0)

include hP hU0 in
theorem PU0_eq : P * U0 = U0 := by
  calc P * U0 = P * (P * U0 * P) := congrArg (P * ·) hU0
    _ = (P * P) * U0 * P := by noncomm_ring
    _ = P * U0 * P := by rw [← hP]
    _ = U0 := hU0.symm

include hP hU0 in
theorem U0P_eq : U0 * P = U0 := by
  calc U0 * P = (P * U0 * P) * P := congrArg (· * P) hU0
    _ = P * U0 * (P * P) := by noncomm_ring
    _ = P * U0 * P := by rw [← hP]
    _ = U0 := hU0.symm

include hP hU1 in
theorem PU1_eq : P * U1 = U1 := by
  calc P * U1 = P * (P * U1 * P) := congrArg (P * ·) hU1
    _ = (P * P) * U1 * P := by noncomm_ring
    _ = P * U1 * P := by rw [← hP]
    _ = U1 := hU1.symm

include hP hU1 in
theorem U1P_eq : U1 * P = U1 := by
  calc U1 * P = (P * U1 * P) * P := congrArg (· * P) hU1
    _ = P * U1 * (P * P) := by noncomm_ring
    _ = P * U1 * P := by rw [← hP]
    _ = U1 := hU1.symm

include hP hV0 in
theorem PV0_eq : P * V0 = V0 := by
  calc P * V0 = P * (P * V0 * P) := congrArg (P * ·) hV0
    _ = (P * P) * V0 * P := by noncomm_ring
    _ = P * V0 * P := by rw [← hP]
    _ = V0 := hV0.symm

include hP hV0 in
theorem V0P_eq : V0 * P = V0 := by
  calc V0 * P = (P * V0 * P) * P := congrArg (· * P) hV0
    _ = P * V0 * (P * P) := by noncomm_ring
    _ = P * V0 * P := by rw [← hP]
    _ = V0 := hV0.symm

include hP hV1 in
theorem PV1_eq : P * V1 = V1 := by
  calc P * V1 = P * (P * V1 * P) := congrArg (P * ·) hV1
    _ = (P * P) * V1 * P := by noncomm_ring
    _ = P * V1 * P := by rw [← hP]
    _ = V1 := hV1.symm

include hP hV1 in
theorem V1P_eq : V1 * P = V1 := by
  calc V1 * P = (P * V1 * P) * P := congrArg (· * P) hV1
    _ = P * V1 * (P * P) := by noncomm_ring
    _ = P * V1 * P := by rw [← hP]
    _ = V1 := hV1.symm

include hP hU0 hV0 hV0U0 in
theorem E0_idem : (U0 * V0) * (U0 * V0) = U0 * V0 := by
  calc U0 * V0 * (U0 * V0) = U0 * (V0 * U0) * V0 := by noncomm_ring
    _ = U0 * P * V0 := by rw [hV0U0]
    _ = U0 * V0 := by rw [mul_assoc, PV0_eq hP hV0]

include hP hU1 hV1 hV1U1 in
theorem E1_idem : (U1 * V1) * (U1 * V1) = U1 * V1 := by
  calc U1 * V1 * (U1 * V1) = U1 * (V1 * U1) * V1 := by noncomm_ring
    _ = U1 * P * V1 := by rw [hV1U1]
    _ = U1 * V1 := by rw [mul_assoc, PV1_eq hP hV1]

include hV0U1 in
theorem E0E1_zero : (U0 * V0) * (U1 * V1) = 0 := by
  calc U0 * V0 * (U1 * V1) = U0 * (V0 * U1) * V1 := by noncomm_ring
    _ = U0 * 0 * V1 := by rw [hV0U1]
    _ = 0 := by noncomm_ring

include hV1U0 in
theorem E1E0_zero : (U1 * V1) * (U0 * V0) = 0 := by
  calc U1 * V1 * (U0 * V0) = U1 * (V1 * U0) * V0 := by noncomm_ring
    _ = U1 * 0 * V0 := by rw [hV1U0]
    _ = 0 := by noncomm_ring

include hP hV0 in
/-- The second split in equation (22): `E0 = U0U0V0V0 + U0U1V1V0`, using
`U0V0 + U1V1 = P` and `P * V0 = V0`. -/
theorem E0_split (hsum : U0 * V0 + U1 * V1 = P) :
    U0 * U0 * (V0 * V0) + U0 * U1 * (V1 * V0) = U0 * V0 := by
  calc U0 * U0 * (V0 * V0) + U0 * U1 * (V1 * V0)
      = U0 * ((U0 * V0 + U1 * V1) * V0) := by noncomm_ring
    _ = U0 * (P * V0) := by rw [hsum]
    _ = U0 * V0 := by rw [PV0_eq hP hV0]

include hP hU0 hV0 hV0U0 in
/-- `V00 U00 = P`, where `U00 = U0U0`, `V00 = V0V0` — equation (17)'s equivalence data for
the corner `E00`. -/
theorem V00U00_eq_P : (V0 * V0) * (U0 * U0) = P := by
  calc V0 * V0 * (U0 * U0) = V0 * (V0 * U0) * U0 := by noncomm_ring
    _ = V0 * P * U0 := by rw [hV0U0]
    _ = V0 * U0 := by rw [mul_assoc, PU0_eq hP hU0]
    _ = P := hV0U0

include hP hU1 hV0 hV0U0 hV1U1 in
/-- `V01 U01 = P`, where `U01 = U0U1`, `V01 = V1V0` — equation (17)'s equivalence data for
the corner `E01`. -/
theorem V01U01_eq_P : (V1 * V0) * (U0 * U1) = P := by
  calc V1 * V0 * (U0 * U1) = V1 * (V0 * U0) * U1 := by noncomm_ring
    _ = V1 * P * U1 := by rw [hV0U0]
    _ = V1 * U1 := by rw [mul_assoc, PU1_eq hP hU1]
    _ = P := hV1U1

include hP hV1 hV1U1 in
/-- The uniform derivation of equation (17)'s equivalence data: GIVEN `Vv * Uv = P`,
`P * Vv = Vv`, `Uv * P = Uv` (and the fixed corner-1 data `V1U1 = P`), `d_v := U1*Vv`,
`d*_v := Uv*V1` automatically satisfy all four relations of (17) with respect to
`Ev := Uv*Vv` and `E1 := U1*V1` — independent of `Uv, Vv`'s further structure. This single
lemma instantiates to `v ∈ {0, 00, 01}`. -/
theorem uniform_17_data {Uv Vv : R} (hVvUv : Vv * Uv = P) (hPVv : P * Vv = Vv)
    (hUvP : Uv * P = Uv) :
    (U1 * V1) * (U1 * Vv) * (Uv * Vv) = U1 * Vv ∧
      (Uv * Vv) * (Uv * V1) * (U1 * V1) = Uv * V1 ∧
      (Uv * V1) * (U1 * Vv) = Uv * Vv ∧
      (U1 * Vv) * (Uv * V1) = U1 * V1 := by
  have hPP : P * P = P := hP.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (U1 * V1) * (U1 * Vv) * (Uv * Vv) = U1 * (V1 * U1) * (Vv * Uv) * Vv := by noncomm_ring
      _ = U1 * P * P * Vv := by rw [hV1U1, hVvUv]
      _ = U1 * (P * P) * Vv := by noncomm_ring
      _ = U1 * P * Vv := by rw [hPP]
      _ = U1 * (P * Vv) := by noncomm_ring
      _ = U1 * Vv := by rw [hPVv]
  · calc (Uv * Vv) * (Uv * V1) * (U1 * V1) = Uv * (Vv * Uv) * (V1 * U1) * V1 := by noncomm_ring
      _ = Uv * P * P * V1 := by rw [hVvUv, hV1U1]
      _ = Uv * (P * P) * V1 := by noncomm_ring
      _ = Uv * P * V1 := by rw [hPP]
      _ = Uv * (P * V1) := by noncomm_ring
      _ = Uv * V1 := by rw [PV1_eq hP hV1]
  · calc (Uv * V1) * (U1 * Vv) = Uv * (V1 * U1) * Vv := by noncomm_ring
      _ = Uv * P * Vv := by rw [hV1U1]
      _ = (Uv * P) * Vv := by noncomm_ring
      _ = Uv * Vv := by rw [hUvP]
  · calc (U1 * Vv) * (Uv * V1) = U1 * (Vv * Uv) * V1 := by noncomm_ring
      _ = U1 * P * V1 := by rw [hVvUv]
      _ = U1 * (P * V1) := by noncomm_ring
      _ = U1 * V1 := by rw [PV1_eq hP hV1]

include hP hV0 in
theorem PV00_eq : P * (V0 * V0) = V0 * V0 := by
  rw [← mul_assoc, PV0_eq hP hV0]

include hP hU0 in
theorem U00P_eq : (U0 * U0) * P = U0 * U0 := by
  rw [mul_assoc, U0P_eq hP hU0]

include hP hV0 hV1 in
theorem PV01_eq : P * (V1 * V0) = V1 * V0 := by
  rw [← mul_assoc, PV1_eq hP hV1]

include hP hU0 hU1 in
theorem U01P_eq : (U0 * U1) * P = U0 * U1 := by
  rw [mul_assoc, U1P_eq hP hU1]

/-- If `a, b` both commute with every value of `ψ`, so does `a * b`. -/
theorem commute_psi_mul {psi : R → R} {a b : R} (ha : ∀ c, a * psi c = psi c * a)
    (hb : ∀ c, b * psi c = psi c * b) (c : R) : (a * b) * psi c = psi c * (a * b) := by
  calc a * b * psi c = a * (b * psi c) := by noncomm_ring
    _ = a * (psi c * b) := by rw [hb]
    _ = (a * psi c) * b := by noncomm_ring
    _ = (psi c * a) * b := by rw [ha]
    _ = psi c * (a * b) := by noncomm_ring

/-- If `a, b` both commute with every value of `ψ`, so does `a + b`. -/
theorem commute_psi_add {psi : R → R} {a b : R} (ha : ∀ c, a * psi c = psi c * a)
    (hb : ∀ c, b * psi c = psi c * b) (c : R) : (a + b) * psi c = psi c * (a + b) := by
  rw [add_mul, ha, hb, mul_add]

/-- Any corner `Uv*Vv` with `Vv*Uv = P` and `P*Vv = Vv` is idempotent — the generic form of
`E0_idem`/`E1_idem`, reusable for `E00, E01` too. -/
theorem Ev_idem {Uv Vv : R} (hVvUv : Vv * Uv = P) (hPVv : P * Vv = Vv) :
    (Uv * Vv) * (Uv * Vv) = Uv * Vv := by
  calc Uv * Vv * (Uv * Vv) = Uv * (Vv * Uv) * Vv := by noncomm_ring
    _ = Uv * P * Vv := by rw [hVvUv]
    _ = Uv * (P * Vv) := by noncomm_ring
    _ = Uv * Vv := by rw [hPVv]

include hP hU0 hV0 hV0U0 hV0U1 in
/-- `E00 * E01 = 0`, the orthogonality `Lemma 4.5` will need for the second split. -/
theorem E00E01_zero : (U0 * U0 * (V0 * V0)) * (U0 * U1 * (V1 * V0)) = 0 := by
  calc U0 * U0 * (V0 * V0) * (U0 * U1 * (V1 * V0))
      = U0 * U0 * V0 * (V0 * U0) * U1 * V1 * V0 := by noncomm_ring
    _ = U0 * U0 * V0 * P * U1 * V1 * V0 := by rw [hV0U0]
    _ = U0 * U0 * (V0 * P) * U1 * V1 * V0 := by noncomm_ring
    _ = U0 * U0 * V0 * U1 * V1 * V0 := by rw [V0P_eq hP hV0]
    _ = U0 * U0 * (V0 * U1) * V1 * V0 := by noncomm_ring
    _ = U0 * U0 * 0 * V1 * V0 := by rw [hV0U1]
    _ = 0 := by noncomm_ring

include hP hU0 hV0 hV0U0 hV1U0 in
/-- `E01 * E00 = 0`, the orthogonality `Lemma 4.5` will need for the second split. -/
theorem E01E00_zero : (U0 * U1 * (V1 * V0)) * (U0 * U0 * (V0 * V0)) = 0 := by
  calc U0 * U1 * (V1 * V0) * (U0 * U0 * (V0 * V0))
      = U0 * U1 * V1 * (V0 * U0) * U0 * V0 * V0 := by noncomm_ring
    _ = U0 * U1 * V1 * P * U0 * V0 * V0 := by rw [hV0U0]
    _ = U0 * U1 * V1 * (P * U0) * V0 * V0 := by noncomm_ring
    _ = U0 * U1 * V1 * U0 * V0 * V0 := by rw [PU0_eq hP hU0]
    _ = U0 * U1 * (V1 * U0) * V0 * V0 := by noncomm_ring
    _ = U0 * U1 * 0 * V0 * V0 := by rw [hV1U0]
    _ = 0 := by noncomm_ring

include hV0U1 in
theorem E00E1_zero : (U0 * U0 * (V0 * V0)) * (U1 * V1) = 0 := by
  calc U0 * U0 * (V0 * V0) * (U1 * V1) = U0 * U0 * V0 * (V0 * U1) * V1 := by noncomm_ring
    _ = U0 * U0 * V0 * 0 * V1 := by rw [hV0U1]
    _ = 0 := by noncomm_ring

include hV1U0 in
theorem E1E00_zero : (U1 * V1) * (U0 * U0 * (V0 * V0)) = 0 := by
  calc U1 * V1 * (U0 * U0 * (V0 * V0)) = U1 * (V1 * U0) * U0 * V0 * V0 := by noncomm_ring
    _ = U1 * 0 * U0 * V0 * V0 := by rw [hV1U0]
    _ = 0 := by noncomm_ring

include hV0U1 in
theorem E01E1_zero : (U0 * U1 * (V1 * V0)) * (U1 * V1) = 0 := by
  calc U0 * U1 * (V1 * V0) * (U1 * V1) = U0 * U1 * V1 * (V0 * U1) * V1 := by noncomm_ring
    _ = U0 * U1 * V1 * 0 * V1 := by rw [hV0U1]
    _ = 0 := by noncomm_ring

include hV1U0 in
theorem E1E01_zero : (U1 * V1) * (U0 * U1 * (V1 * V0)) = 0 := by
  calc U1 * V1 * (U0 * U1 * (V1 * V0)) = U1 * (V1 * U0) * U1 * V1 * V0 := by noncomm_ring
    _ = U1 * 0 * U1 * V1 * V0 := by rw [hV1U0]
    _ = 0 := by noncomm_ring

end Theorem41Setup
section Theorem41Final

variable (psi : R → R)
  (hpsi_add : ∀ a b : R, psi (a + b) = psi a + psi b)
  (hpsi_mul : ∀ a b : R, psi (a * b) = psi a * psi b)
  {P U0 U1 V0 V1 : R} (hPdef : P = psi 1) (hU0 : U0 = P * U0 * P) (hU1 : U1 = P * U1 * P)
  (hV0 : V0 = P * V0 * P) (hV1 : V1 = P * V1 * P)
  (hV0U0 : V0 * U0 = P) (hV1U1 : V1 * U1 = P) (hV0U1 : V0 * U1 = 0) (hV1U0 : V1 * U0 = 0)
  (hsum : U0 * V0 + U1 * V1 = P)
  (hU0psi : ∀ c : R, U0 * psi c = psi c * U0) (hU1psi : ∀ c : R, U1 * psi c = psi c * U1)
  (hV0psi : ∀ c : R, V0 * psi c = psi c * V0) (hV1psi : ∀ c : R, V1 * psi c = psi c * V1)

include hpsi_mul hPdef in
/-- `P² = P`, from `P = ψ(1)` and `ψ` multiplicative. -/
theorem hP_eq : P = P * P := by
  conv_lhs => rw [hPdef]
  rw [hPdef, ← hpsi_mul, one_mul]

include hpsi_mul hPdef in
/-- `P` commutes with `ψ(R)` for free, from `P = ψ(1)` and the ring identities `1·a = a·1 = a`
(no further hypothesis on `P` needed). -/
theorem hP_psi : ∀ a : R, P * psi a = psi a * P := by
  intro a
  rw [hPdef, ← hpsi_mul, ← hpsi_mul, one_mul, mul_one]

include hpsi_mul hPdef in
/-- `θ(z) = z_P` (the original coefficient map `a ↦ ψ(a)` equals the `P`-corner coefficient
map, since `ψ(a)P = ψ(a)` from `ψ` multiplicative and `P = ψ(1)`). Stated for arbitrary `n`
since it does not need Theorem 4.1's specific hypotheses, only `ψ` and `P = ψ(1)`. -/
theorem steinCoeffMap_psi_eq_P
    (haddP : ∀ a b : R, psi (a + b) * P = psi a * P + psi b * P)
    (hmulP : ∀ a b : R, psi (a * b) * P = (psi a * P) * (psi b * P))
    (z : SteinbergGroup n R) :
    steinCoeffMap psi hpsi_add hpsi_mul z = steinCoeffMap (fun a => psi a * P) haddP hmulP z := by
  have hagree : steinCoeffMap psi hpsi_add hpsi_mul =
      steinCoeffMap (fun a => psi a * P) haddP hmulP :=
    PresentedGroup.ext (rels := steinRelations n R) (fun w => by
      show steinCoeffMap psi hpsi_add hpsi_mul (SteinbergGroup.x w.i w.j w.hij w.a) =
        steinCoeffMap (fun a => psi a * P) haddP hmulP (SteinbergGroup.x w.i w.j w.hij w.a)
      rw [steinCoeffMap_x, steinCoeffMap_x]
      congr 1
      rw [hPdef, ← hpsi_mul, mul_one])
  exact congrFun (congrArg (fun f => f.toFun) hagree) z

/-- The coefficient map only depends on the corner `Q` up to its VALUE, not its syntactic
form — needed to convert `z_{E00+E01}` to `z_{E0}` (and `z_{E0+E1}` to `z_P`) along an
equation like `E00_split` that is propositional, not definitional. -/
theorem steinCoeffMap_congr_corner {Q1 Q2 : R} (hQQ : Q1 = Q2)
    (hadd1 : ∀ a b : R, psi (a + b) * Q1 = psi a * Q1 + psi b * Q1)
    (hmul1 : ∀ a b : R, psi (a * b) * Q1 = (psi a * Q1) * (psi b * Q1))
    (hadd2 : ∀ a b : R, psi (a + b) * Q2 = psi a * Q2 + psi b * Q2)
    (hmul2 : ∀ a b : R, psi (a * b) * Q2 = (psi a * Q2) * (psi b * Q2))
    (z : SteinbergGroup n R) :
    steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 z =
      steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 z := by
  have hagree : steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1 =
      steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 :=
    PresentedGroup.ext (rels := steinRelations n R) (fun w => by
      show steinCoeffMap (fun a => psi a * Q1) hadd1 hmul1
          (SteinbergGroup.x w.i w.j w.hij w.a) =
        steinCoeffMap (fun a => psi a * Q2) hadd2 hmul2 (SteinbergGroup.x w.i w.j w.hij w.a)
      rw [steinCoeffMap_x, steinCoeffMap_x]
      congr 1
      rw [hQQ])
  exact congrFun (congrArg (fun f => f.toFun) hagree) z

include hpsi_add hpsi_mul hPdef hU0 hU1 hV0 hV1 hV0U0 hV1U1 hV0U1 hV1U0 hsum
  hU0psi hU1psi hV0psi hV1psi in
/-- **Theorem 4.1** (annihilating the Steinberg kernel): `θ` kills every element of `ker π`. -/
theorem theorem_4_1 (z : SteinbergGroup 6 R) (hz : steinPi z = 1) :
    steinCoeffMap psi hpsi_add hpsi_mul z = 1 := by
  have hP : P = P * P := hP_eq psi hpsi_mul hPdef
  have hex6 : ∀ i j : Fin 6, i ≠ j → ∃ k0 : Fin 6, k0 ≠ i ∧ k0 ≠ j := by decide
  have hE0E0 := E0_idem hP hU0 hV0 hV0U0
  have hE1E1 := E1_idem hP hU1 hV1 hV1U1
  have hE0E1 := E0E1_zero (R := R) (U0 := U0) (V1 := V1) (hV0U1 := hV0U1)
  have hE1E0 := E1E0_zero (R := R) (U1 := U1) (V0 := V0) (hV1U0 := hV1U0)
  have hE0psi : ∀ a : R, (U0 * V0) * psi a = psi a * (U0 * V0) := commute_psi_mul hU0psi hV0psi
  have hE1psi : ∀ a : R, (U1 * V1) * psi a = psi a * (U1 * V1) := commute_psi_mul hU1psi hV1psi
  -- v = 0
  have h17_0 := uniform_17_data hP hV1 hV1U1 (Uv := U0) (Vv := V0) hV0U0
    (PV0_eq hP hV0) (U0P_eq hP hU0)
  have hd0psi : ∀ a : R, (U1 * V0) * psi a = psi a * (U1 * V0) := commute_psi_mul hU1psi hV0psi
  have hdstar0psi : ∀ a : R, (U0 * V1) * psi a = psi a * (U0 * V1) :=
    commute_psi_mul hU0psi hV1psi
  have hzE0 := lemma_4_4 (E := U0 * V0) (F := U1 * V1) (d := U1 * V0) (dstar := U0 * V1)
    (hEE := hE0E0) (hFF := hE1E1) (hEF := hE0E1) (hFE := hE1E0)
    (hd := h17_0.1.symm) (hdstar := h17_0.2.1.symm)
    (hdstard := h17_0.2.2.1) (hddstar := h17_0.2.2.2)
    (psi := psi) (hpsi_add := hpsi_add) (hpsi_mul := hpsi_mul)
    (hEpsi := hE0psi) (hFpsi := hE1psi) (hdpsi := hd0psi) (hdstarpsi := hdstar0psi)
    (haddE := steinLam_add psi hpsi_add (U0 * V0))
    (hmulE := steinLam_mul psi hpsi_mul (U0 * V0) hE0psi hE0E0)
    (haddF := steinLam_add psi hpsi_add (U1 * V1))
    (hmulF := steinLam_mul psi hpsi_mul (U1 * V1) hE1psi hE1E1) z hz
  -- v = 00
  have hU00psi : ∀ a : R, (U0 * U0) * psi a = psi a * (U0 * U0) := commute_psi_mul hU0psi hU0psi
  have hV00psi : ∀ a : R, (V0 * V0) * psi a = psi a * (V0 * V0) := commute_psi_mul hV0psi hV0psi
  have hE00E00 := Ev_idem (R := R) (P := P) (V00U00_eq_P hP hU0 hV0 hV0U0) (PV00_eq hP hV0)
  have hE00psi : ∀ a : R, (U0 * U0 * (V0 * V0)) * psi a = psi a * (U0 * U0 * (V0 * V0)) :=
    commute_psi_mul hU00psi hV00psi
  have h17_00 := uniform_17_data hP hV1 hV1U1 (Uv := U0 * U0) (Vv := V0 * V0)
    (V00U00_eq_P hP hU0 hV0 hV0U0) (PV00_eq hP hV0) (U00P_eq hP hU0)
  have hd00psi : ∀ a : R, (U1 * (V0 * V0)) * psi a = psi a * (U1 * (V0 * V0)) :=
    commute_psi_mul hU1psi hV00psi
  have hdstar00psi : ∀ a : R, (U0 * U0 * V1) * psi a = psi a * (U0 * U0 * V1) :=
    commute_psi_mul hU00psi hV1psi
  have hzE00 := lemma_4_4 (E := U0 * U0 * (V0 * V0)) (F := U1 * V1) (d := U1 * (V0 * V0))
    (dstar := U0 * U0 * V1)
    (hEE := hE00E00) (hFF := hE1E1) (hEF := E00E1_zero (R := R) (U0 := U0) (V1 := V1) (hV0U1 := hV0U1))
    (hFE := E1E00_zero (R := R) (U1 := U1) (V0 := V0) (hV1U0 := hV1U0))
    (hd := h17_00.1.symm) (hdstar := h17_00.2.1.symm)
    (hdstard := h17_00.2.2.1) (hddstar := h17_00.2.2.2)
    (psi := psi) (hpsi_add := hpsi_add) (hpsi_mul := hpsi_mul)
    (hEpsi := hE00psi) (hFpsi := hE1psi) (hdpsi := hd00psi) (hdstarpsi := hdstar00psi)
    (haddE := steinLam_add psi hpsi_add (U0 * U0 * (V0 * V0)))
    (hmulE := steinLam_mul psi hpsi_mul (U0 * U0 * (V0 * V0)) hE00psi hE00E00)
    (haddF := steinLam_add psi hpsi_add (U1 * V1))
    (hmulF := steinLam_mul psi hpsi_mul (U1 * V1) hE1psi hE1E1) z hz
  -- v = 01
  have hU01psi : ∀ a : R, (U0 * U1) * psi a = psi a * (U0 * U1) := commute_psi_mul hU0psi hU1psi
  have hV01psi : ∀ a : R, (V1 * V0) * psi a = psi a * (V1 * V0) := commute_psi_mul hV1psi hV0psi
  have hE01E01 := Ev_idem (R := R) (P := P)
    (V01U01_eq_P hP hU1 hV0 hV0U0 hV1U1) (PV01_eq hP hV0 hV1)
  have hE01psi : ∀ a : R, (U0 * U1 * (V1 * V0)) * psi a = psi a * (U0 * U1 * (V1 * V0)) :=
    commute_psi_mul hU01psi hV01psi
  have h17_01 := uniform_17_data hP hV1 hV1U1 (Uv := U0 * U1) (Vv := V1 * V0)
    (V01U01_eq_P hP hU1 hV0 hV0U0 hV1U1) (PV01_eq hP hV0 hV1) (U01P_eq hP hU0 hU1)
  have hd01psi : ∀ a : R, (U1 * (V1 * V0)) * psi a = psi a * (U1 * (V1 * V0)) :=
    commute_psi_mul hU1psi hV01psi
  have hdstar01psi : ∀ a : R, (U0 * U1 * V1) * psi a = psi a * (U0 * U1 * V1) :=
    commute_psi_mul hU01psi hV1psi
  have hzE01 := lemma_4_4 (E := U0 * U1 * (V1 * V0)) (F := U1 * V1) (d := U1 * (V1 * V0))
    (dstar := U0 * U1 * V1)
    (hEE := hE01E01) (hFF := hE1E1) (hEF := E01E1_zero (R := R) (U0 := U0) (V1 := V1) (hV0U1 := hV0U1))
    (hFE := E1E01_zero (R := R) (U1 := U1) (V0 := V0) (hV1U0 := hV1U0))
    (hd := h17_01.1.symm) (hdstar := h17_01.2.1.symm)
    (hdstard := h17_01.2.2.1) (hddstar := h17_01.2.2.2)
    (psi := psi) (hpsi_add := hpsi_add) (hpsi_mul := hpsi_mul)
    (hEpsi := hE01psi) (hFpsi := hE1psi) (hdpsi := hd01psi) (hdstarpsi := hdstar01psi)
    (haddE := steinLam_add psi hpsi_add (U0 * U1 * (V1 * V0)))
    (hmulE := steinLam_mul psi hpsi_mul (U0 * U1 * (V1 * V0)) hE01psi hE01E01)
    (haddF := steinLam_add psi hpsi_add (U1 * V1))
    (hmulF := steinLam_mul psi hpsi_mul (U1 * V1) hE1psi hE1E1) z hz
  -- equation (23): z_E0 = z_E1 = z_E00 = z_E01
  have hchain : steinCoeffMap (fun a => psi a * (U0 * V0))
        ((steinLam_add psi hpsi_add (U0 * V0)))
        ((steinLam_mul psi hpsi_mul (U0 * V0) hE0psi hE0E0)) z =
      steinCoeffMap (fun a => psi a * (U0 * U0 * (V0 * V0)))
        ((steinLam_add psi hpsi_add (U0 * U0 * (V0 * V0))))
        ((steinLam_mul psi hpsi_mul (U0 * U0 * (V0 * V0)) hE00psi hE00E00)) z := hzE0.trans hzE00.symm
  have hchain2 : steinCoeffMap (fun a => psi a * (U0 * V0))
        ((steinLam_add psi hpsi_add (U0 * V0)))
        ((steinLam_mul psi hpsi_mul (U0 * V0) hE0psi hE0E0)) z =
      steinCoeffMap (fun a => psi a * (U0 * U1 * (V1 * V0)))
        ((steinLam_add psi hpsi_add (U0 * U1 * (V1 * V0))))
        ((steinLam_mul psi hpsi_mul (U0 * U1 * (V1 * V0)) hE01psi hE01E01)) z := hzE0.trans hzE01.symm
  -- E0 = E00 + E01, via the orthogonal-sum decomposition and E0_split
  have hE00E01 := E00E01_zero (V1 := V1) hP hU0 hV0 hV0U0 hV0U1
  have hE01E00 := E01E00_zero (U1 := U1) hP hU0 hV0 hV0U0 hV1U0
  have hEsumE0_idem := orthogonal_idem_sum hE00E00 hE01E01 hE00E01 hE01E00
  have hEsumE0_psi := commute_psi_add hE00psi hE01psi
  have hsplit := steinCoeffMap_orthogonal_sum (Q1 := U0 * U0 * (V0 * V0))
    (Q2 := U0 * U1 * (V1 * V0)) (hQ1Q1 := hE00E00) (hQ2Q2 := hE01E01)
    (hQ1Q2 := hE00E01) (hQ2Q1 := hE01E00) (psi := psi) (hQ1psi := hE00psi) (hQ2psi := hE01psi)
    (hadd1 := (steinLam_add psi hpsi_add (U0 * U0 * (V0 * V0))))
    (hmul1 := (steinLam_mul psi hpsi_mul (U0 * U0 * (V0 * V0)) hE00psi hE00E00))
    (hadd2 := (steinLam_add psi hpsi_add (U0 * U1 * (V1 * V0))))
    (hmul2 := (steinLam_mul psi hpsi_mul (U0 * U1 * (V1 * V0)) hE01psi hE01E01))
    (haddQ := (steinLam_add psi hpsi_add (U0 * U0 * (V0 * V0) + U0 * U1 * (V1 * V0))))
    (hmulQ := (steinLam_mul psi hpsi_mul (U0 * U0 * (V0 * V0) + U0 * U1 * (V1 * V0)) hEsumE0_psi hEsumE0_idem))
    (hex := hex6) z
  have hE0split := E0_split (R := R) (P := P) (U0 := U0) (U1 := U1) (V0 := V0) (V1 := V1)
    hP hV0 hsum
  have hsplit' := steinCoeffMap_congr_corner (psi := psi) hE0split
    ((steinLam_add psi hpsi_add (U0 * U0 * (V0 * V0) + U0 * U1 * (V1 * V0))))
    ((steinLam_mul psi hpsi_mul (U0 * U0 * (V0 * V0) + U0 * U1 * (V1 * V0)) hEsumE0_psi hEsumE0_idem))
    ((steinLam_add psi hpsi_add (U0 * V0)))
    ((steinLam_mul psi hpsi_mul (U0 * V0) hE0psi hE0E0))
    z
  -- Combine: z_E0 = z_E00 * z_E01 = z_E0 * z_E0, so z_E0 = 1 and z_E1 = 1
  have hzE0_sq : steinCoeffMap (fun a => psi a * (U0 * V0))
      ((steinLam_add psi hpsi_add (U0 * V0)))
      ((steinLam_mul psi hpsi_mul (U0 * V0) hE0psi hE0E0)) z *
      steinCoeffMap (fun a => psi a * (U0 * V0))
      ((steinLam_add psi hpsi_add (U0 * V0)))
      ((steinLam_mul psi hpsi_mul (U0 * V0) hE0psi hE0E0)) z =
      steinCoeffMap (fun a => psi a * (U0 * V0))
      ((steinLam_add psi hpsi_add (U0 * V0)))
      ((steinLam_mul psi hpsi_mul (U0 * V0) hE0psi hE0E0)) z :=
    (congrArg₂ (· * ·) hchain hchain2).trans (hsplit.symm.trans hsplit')
  have hzE0_eq_one : steinCoeffMap (fun a => psi a * (U0 * V0))
      ((steinLam_add psi hpsi_add (U0 * V0)))
      ((steinLam_mul psi hpsi_mul (U0 * V0) hE0psi hE0E0)) z = 1 := by
    have := hzE0_sq
    set w := steinCoeffMap (fun a => psi a * (U0 * V0))
      ((steinLam_add psi hpsi_add (U0 * V0)))
      ((steinLam_mul psi hpsi_mul (U0 * V0) hE0psi hE0E0)) z with hw_def
    have hww : w * w = w := this
    calc w = w⁻¹ * (w * w) := by group
      _ = w⁻¹ * w := by rw [hww]
      _ = 1 := by group
  have hzE1_eq_one : steinCoeffMap (fun a => psi a * (U1 * V1))
      ((steinLam_add psi hpsi_add (U1 * V1)))
      ((steinLam_mul psi hpsi_mul (U1 * V1) hE1psi hE1E1)) z = 1 := by
    have heq : steinCoeffMap (fun a => psi a * (U1 * V1))
        ((steinLam_add psi hpsi_add (U1 * V1)))
        ((steinLam_mul psi hpsi_mul (U1 * V1) hE1psi hE1E1)) z =
        steinCoeffMap (fun a => psi a * (U0 * V0))
          ((steinLam_add psi hpsi_add (U0 * V0)))
          ((steinLam_mul psi hpsi_mul (U0 * V0) hE0psi hE0E0)) z := hzE0.symm
    rw [heq, hzE0_eq_one]
  -- The first split: θ(z) = z_P = z_E0 * z_E1 = 1
  have hE0E1_idem := orthogonal_idem_sum hE0E0 hE1E1 hE0E1 hE1E0
  have hE0E1_psi := commute_psi_add hE0psi hE1psi
  have hPsplit := steinCoeffMap_orthogonal_sum (Q1 := U0 * V0) (Q2 := U1 * V1)
    (hQ1Q1 := hE0E0) (hQ2Q2 := hE1E1) (hQ1Q2 := hE0E1) (hQ2Q1 := hE1E0) (psi := psi)
    (hQ1psi := hE0psi) (hQ2psi := hE1psi)
    (hadd1 := (steinLam_add psi hpsi_add (U0 * V0)))
    (hmul1 := (steinLam_mul psi hpsi_mul (U0 * V0) hE0psi hE0E0))
    (hadd2 := (steinLam_add psi hpsi_add (U1 * V1)))
    (hmul2 := (steinLam_mul psi hpsi_mul (U1 * V1) hE1psi hE1E1))
    (haddQ := (steinLam_add psi hpsi_add (U0 * V0 + U1 * V1)))
    (hmulQ := (steinLam_mul psi hpsi_mul (U0 * V0 + U1 * V1) hE0E1_psi hE0E1_idem))
    (hex := hex6) z
  have hPpsi := hP_psi psi hpsi_mul hPdef
  have haddP := (steinLam_add psi hpsi_add (P))
  have hmulP := (steinLam_mul psi hpsi_mul (P) hPpsi hP.symm)
  have hPsplit' := steinCoeffMap_congr_corner (psi := psi) hsum
    ((steinLam_add psi hpsi_add (U0 * V0 + U1 * V1)))
    ((steinLam_mul psi hpsi_mul (U0 * V0 + U1 * V1) hE0E1_psi hE0E1_idem))
    haddP hmulP z
  -- θ(z) = z_P = z_{E0+E1} = z_E0 * z_E1 = 1 * 1 = 1
  have hpure := steinCoeffMap_psi_eq_P psi hpsi_add hpsi_mul hPdef haddP hmulP z
  rw [hpure, ← hPsplit', hPsplit, hzE0_eq_one, hzE1_eq_one, one_mul]

end Theorem41Final

end FiniteAlgebraicEnvelopes
end OAI

open OAI.FiniteAlgebraicEnvelopes

universe u

theorem solution {R : Type u} [Ring R] (psi : R → R)
    (hpsi_add : ∀ a b : R, psi (a + b) = psi a + psi b)
    (hpsi_mul : ∀ a b : R, psi (a * b) = psi a * psi b)
    {P U0 U1 V0 V1 : R} (hPdef : P = psi 1) (hU0 : U0 = P * U0 * P) (hU1 : U1 = P * U1 * P)
    (hV0 : V0 = P * V0 * P) (hV1 : V1 = P * V1 * P)
    (hV0U0 : V0 * U0 = P) (hV1U1 : V1 * U1 = P) (hV0U1 : V0 * U1 = 0) (hV1U0 : V1 * U0 = 0)
    (hsum : U0 * V0 + U1 * V1 = P)
    (hU0psi : ∀ c : R, U0 * psi c = psi c * U0) (hU1psi : ∀ c : R, U1 * psi c = psi c * U1)
    (hV0psi : ∀ c : R, V0 * psi c = psi c * V0) (hV1psi : ∀ c : R, V1 * psi c = psi c * V1)
    (z : SteinbergGroup 6 R) (hz : steinPi z = 1) :
    steinCoeffMap psi hpsi_add hpsi_mul z = 1 :=
  theorem_4_1 psi hpsi_add hpsi_mul hPdef hU0 hU1 hV0 hV1 hV0U0 hV1U1 hV0U1 hV1U0 hsum
    hU0psi hU1psi hV0psi hV1psi z hz
