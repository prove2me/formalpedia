-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_addSubgroup_mem_iff_isGoodClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2ce59cd4-eb40-5d22-9ab6-b221983a5a06

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_addSubgroup_mem_iff_isGoodClass
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace GoodClassGroup

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

theorem fstDiv_add (D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.fstDiv (D + D') = P.fstDiv D + P.fstDiv D' := by
  classical
  simp only [PlaceSpecialization.fstDiv]
  exact Finsupp.filter_add

theorem fstDiv_neg (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.fstDiv (-D) = -P.fstDiv D := by
  classical
  simp only [PlaceSpecialization.fstDiv]
  exact Finsupp.filter_neg _ _

theorem sndDiv_add (D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.sndDiv (D + D') = P.sndDiv D + P.sndDiv D' := by
  classical
  simp only [PlaceSpecialization.sndDiv]
  exact Finsupp.filter_add

theorem sndDiv_neg (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.sndDiv (-D) = -P.sndDiv D := by
  classical
  simp only [PlaceSpecialization.sndDiv]
  exact Finsupp.filter_neg _ _

theorem glueData_add
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.glueData S (D + D') = P.glueData S D + P.glueData S D' := by
  simp only [PlaceSpecialization.glueData, fstDiv_add, sndDiv_add, Finsupp.mapDomain_add,
    Prod.mk_add_mk, add_zero]

theorem glueData_neg
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.glueData S (-D) = -P.glueData S D := by
  have h := glueData_add P S (-D) D
  rwa [neg_add_cancel, P.glueData_zero, eq_comm, add_eq_zero_iff_eq_neg] at h

theorem isGoodDiv_add {D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hD : P.IsGoodDiv D) (hD' : P.IsGoodDiv D') : P.IsGoodDiv (D + D') := by
  classical
  intro W hW
  rcases Finset.mem_union.mp (Finsupp.support_add hW) with h | h
  · exact hD W h
  · exact hD' W h

theorem isGoodDiv_neg {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hD : P.IsGoodDiv D) : P.IsGoodDiv (-D) := by
  intro W hW
  exact hD W (by simpa using hW)

theorem isGoodClass_add
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    {x y : JZero (N * q)} (hx : P.IsGoodClass S x) (hy : P.IsGoodClass S y) :
    P.IsGoodClass S (x + y) := by
  obtain ⟨D, hgD, haD, hmD⟩ := hx
  obtain ⟨D', hgD', haD', hmD'⟩ := hy
  refine ⟨D + D', isGoodDiv_add P hgD hgD', ?_, ?_⟩
  · show P.glueData S ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        + (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
      ∈ GluingData.admissible S
    rw [glueData_add]
    exact add_mem haD haD'
  · show Pic0.mk (D + D') = x + y
    rw [Pic0.mk_add, hmD, hmD']

theorem isGoodClass_neg
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    {x : JZero (N * q)} (hx : P.IsGoodClass S x) : P.IsGoodClass S (-x) := by
  obtain ⟨D, hgD, haD, hmD⟩ := hx
  refine ⟨-D, isGoodDiv_neg P hgD, ?_, ?_⟩
  · show P.glueData S (-(D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
      ∈ GluingData.admissible S
    rw [glueData_neg]
    exact neg_mem haD
  · show Pic0.mk (-D) = -x
    rw [← hmD]
    rfl

def goodClassSubgroup
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))) :
    AddSubgroup ↥(inertiaInvariants A (N * q)) where
  carrier := {x | P.IsGoodClass S (x : JZero (N * q))}
  zero_mem' := P.isGoodClass_zero S
  add_mem' := fun hx hy => isGoodClass_add P S hx hy
  neg_mem' := fun hx => isGoodClass_neg P S hx

@[scoped simp] theorem mem_goodClassSubgroup
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (x : ↥(inertiaInvariants A (N * q))) :
    x ∈ goodClassSubgroup P S ↔ P.IsGoodClass S (x : JZero (N * q)) :=
  Iff.rfl

theorem exists_addSubgroup_mem_iff_isGoodClass
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))) :
    ∃ K : AddSubgroup ↥(inertiaInvariants A (N * q)),
      ∀ x : ↥(inertiaInvariants A (N * q)), x ∈ K ↔ P.IsGoodClass S (x : JZero (N * q)) :=
  ⟨goodClassSubgroup P S, mem_goodClassSubgroup P S⟩

end GoodClassGroup
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_addSubgroup_mem_iff_isGoodClass.GoodClassGroup"

theorem solution (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] (k : Type*) [Field k]
    [CharP k q] (red : A →+* k) (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))) :
    ∃ K : AddSubgroup ↥(inertiaInvariants A (N * q)),
      ∀ x : ↥(inertiaInvariants A (N * q)), x ∈ K ↔ P.IsGoodClass S (x : JZero (N * q)) :=
  GoodClassGroup.exists_addSubgroup_mem_iff_isGoodClass P S

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_addSubgroup_mem_iff_isGoodClass.GoodClassGroup"

end S_ModularCurve_PlaceSpecialization_exists_addSubgroup_mem_iff_isGoodClass
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_addSubgroup_mem_iff_isGoodClass (solution)
