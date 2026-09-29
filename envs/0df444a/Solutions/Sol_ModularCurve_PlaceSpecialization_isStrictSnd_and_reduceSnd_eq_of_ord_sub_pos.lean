-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/40c9867a-db16-5bb3-89e3-4ff9ca54370f

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint
import Definitions.Def_MDivRepresents
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos.ModularCurve"
p2m_open "ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple.jFun PlaceSpecialization.ProlongationTuple.jQFun PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_congr qExpand_qExpand jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel exists_ramification_frobenius KroneckerCongruence jGeomGen jNGeomGen jGeomGen_sub_algebraMap_ne_zero IsCentreOf frobeniusGeomLevel_jGeomGen_sub_pow PlaceSpecialization.jNQFun"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple reduceFst reduceSnd IsStrictSnd d0_j d1 d0_jN jNQFun"
namespace PlaceDictSnd
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

theorem pos_of_natCast_mul_pos {e : ℕ} {x : ℤ} (h : 0 < (e : ℤ) * x) : 0 < x := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with h' | h'
  · exact h'.2
  · exact absurd h'.1 (not_lt.2 (Int.natCast_nonneg e))

theorem coeffMap_qExpand_aux {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext m
  by_cases h : (n : ℤ) ∣ m
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

section Generators

variable (N q : ℕ) [NeZero N] [NeZero q]

theorem heckeAlphaBar_j :
    heckeAlphaBar (AlgebraicClosure ℚ) N q
        ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩
      = ProlongationTuple.jFun N q :=
  Subtype.ext (coe_heckeAlphaBar N q _)

theorem heckeBetaBar_j :
    heckeBetaBar (AlgebraicClosure ℚ) N q
        ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩
      = ProlongationTuple.jQFun N q := by
  refine Subtype.ext ?_
  rw [coe_heckeBetaBar]
  change qExpand (AlgebraicClosure ℚ) q (coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) jq)
    = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ q jq)
  rw [coeffMap_qExpand_aux]

theorem heckeBetaBar_jN :
    heckeBetaBar (AlgebraicClosure ℚ) N q
        ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩
      = PlaceSpecialization.jNQFun N q := by
  refine Subtype.ext ?_
  rw [coe_heckeBetaBar]
  change qExpand (AlgebraicClosure ℚ) q (coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ N jq))
    = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ (N * q) jq)
  rw [coeffMap_qExpand_aux, coeffMap_qExpand_aux, qExpand_qExpand, qExpand_congr (mul_comm q N)]

end Generators

section Transport

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)
  (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))

theorem ord_pos_reduceFst_j (x : A)
    (h : 0 < W.ord (PlaceSpecialization.ProlongationTuple.jFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (x : AlgebraicClosure ℚ))) :
    0 < (P.reduceFst W).ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (red x)) := by
  have heq : heckeAlphaBar (AlgebraicClosure ℚ) N q
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (x : AlgebraicClosure ℚ))
      = PlaceSpecialization.ProlongationTuple.jFun N q -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (x : AlgebraicClosure ℚ) := by
    rw [map_sub, AlgHom.commutes, heckeAlphaBar_j]
  rw [← heq, Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W] at h
  exact P.d0_j _ x (pos_of_natCast_mul_pos h)

theorem ord_pos_reduceSnd_j (x : A)
    (h : 0 < W.ord (PlaceSpecialization.ProlongationTuple.jQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (x : AlgebraicClosure ℚ))) :
    0 < (P.reduceSnd W).ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (red x)) := by
  have heq : heckeBetaBar (AlgebraicClosure ℚ) N q
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (x : AlgebraicClosure ℚ))
      = PlaceSpecialization.ProlongationTuple.jQFun N q -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (x : AlgebraicClosure ℚ) := by
    rw [map_sub, AlgHom.commutes, heckeBetaBar_j]
  rw [← heq, Place.ord_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ W] at h
  exact P.d0_j _ x (pos_of_natCast_mul_pos h)

theorem ord_pos_reduceSnd_jN (x : A)
    (h : 0 < W.ord (PlaceSpecialization.jNQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (x : AlgebraicClosure ℚ))) :
    0 < (P.reduceSnd W).ord (jNGeomGen k N - algebraMap k (modularFunctionFieldC k N) (red x)) := by
  have heq : heckeBetaBar (AlgebraicClosure ℚ) N q
      (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (x : AlgebraicClosure ℚ))
      = PlaceSpecialization.jNQFun N q -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (x : AlgebraicClosure ℚ) := by
    rw [map_sub, AlgHom.commutes, heckeBetaBar_jN]
  rw [← heq, Place.ord_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ W] at h
  exact P.d0_jN _ x (pos_of_natCast_mul_pos h)

end Transport

section JValue

variable {k : Type*} [Field k] {N : ℕ} [NeZero N]

theorem jGeomGen_mem_of_ord_pos {w : Place k (modularFunctionFieldC k N)} {d : k}
    (h : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) d)) :
    jGeomGen k N ∈ w.toValuationSubring := by
  have hmem : jGeomGen k N - algebraMap k (modularFunctionFieldC k N) d ∈ w.toValuationSubring :=
    w.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N d) h.le
  have := add_mem hmem (w.algebraMap_mem' d)
  rwa [sub_add_cancel] at this

theorem evalAt_jGeomGen_of_ord_pos {w : Place k (modularFunctionFieldC k N)} {d : k}
    (h : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) d)) :
    w.evalAt (jGeomGen k N) = d := by
  have hcongr := w.evalAt_congr (jGeomGen_mem_of_ord_pos h) (w.algebraMap_mem' d) (Or.inr h)
  rw [hcongr, w.evalAt_algebraMap]

theorem jValue_unique {w : Place k (modularFunctionFieldC k N)} {d d' : k}
    (h : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) d))
    (h' : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) d')) : d = d' := by
  rw [← evalAt_jGeomGen_of_ord_pos h, evalAt_jGeomGen_of_ord_pos h']

variable {q : ℕ} [Fact q.Prime] [CharP k q] (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)

theorem jValue_frobOnPlacesGeomLevel {w : Place k (modularFunctionFieldC k N)} {d : k}
    (h : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) d)) :
    0 < (frobOnPlacesGeomLevel k N data hKr w).ord
      (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (d ^ q)) := by
  obtain ⟨e, -, -, hord⟩ := exists_ramification_frobenius k N data hKr w
  have hkey := hord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (d ^ q))
  rw [frobeniusGeomLevel_jGeomGen_sub_pow k N data hKr d, ← zpow_natCast, Place.ord_zpow] at hkey
  have hq : 0 < (q : ℤ) := by exact_mod_cast (Fact.out : q.Prime).pos
  have hpos : 0 < (e : ℤ) * (frobOnPlacesGeomLevel k N data hKr w).ord
      (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (d ^ q)) := by
    rw [← hkey]; exact mul_pos hq h
  exact pos_of_natCast_mul_pos hpos

end JValue

end ModularCurve.PlaceSpecialization.PlaceDictSnd

open ModularCurve.PlaceSpecialization.PlaceDictSnd in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQ : P.IsStrictSnd Q)
    (hsm : ∃ c : k × k, IsCentreOf k N c (P.reduceSnd Q) ∧
      ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceSnd Q)
    (hgen : (P.reduceSnd Q).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jGeomGen k N) ∧
      (P.reduceSnd Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jNGeomGen k N))
    (a b c a' b' c' : A) (ha : red a' = red a) (hb : red b' = red b) (hc : red c' = red c)
    (haQ : 0 < Q.ord (PlaceSpecialization.ProlongationTuple.jQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)))
    (hbQ : 0 < Q.ord (PlaceSpecialization.jNQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ)))
    (hcQ : 0 < Q.ord (PlaceSpecialization.ProlongationTuple.jFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)))
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (haW : 0 < W.ord (PlaceSpecialization.ProlongationTuple.jQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a' : AlgebraicClosure ℚ)))
    (hbW : 0 < W.ord (PlaceSpecialization.jNQFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (b' : AlgebraicClosure ℚ)))
    (hcW : 0 < W.ord (PlaceSpecialization.ProlongationTuple.jFun N q -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c' : AlgebraicClosure ℚ))) :
    P.IsStrictSnd W ∧ P.reduceSnd W = P.reduceSnd Q := by

  have cW : IsCentreOf k N (red a, red b) (P.reduceSnd W) :=
    And.intro (ha ▸ ord_pos_reduceSnd_j P W a' haW) (hb ▸ ord_pos_reduceSnd_jN P W b' hbW)
  have cQ : IsCentreOf k N (red a, red b) (P.reduceSnd Q) :=
    And.intro (ord_pos_reduceSnd_j P Q a haQ) (ord_pos_reduceSnd_jN P Q b hbQ)

  obtain ⟨c₀, hc₀, huniq⟩ := hsm
  have hc₀eq : c₀ = (red a, red b) := hc₀.eq cQ
  have hSnd : P.reduceSnd W = P.reduceSnd Q := huniq _ (by rw [hc₀eq]; exact cW)
  refine ⟨And.intro ?_ ?_, hSnd⟩
  ·
    rcases P.d1 W with h1 | h1
    · exact h1
    · exfalso
      change frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W at h1

      have hva : 0 < (P.reduceSnd Q).ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (red a)) := cQ.1
      have hFW : 0 < (P.reduceFst W).ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (red c)) :=
        hc ▸ ord_pos_reduceFst_j P W c' hcW
      have hFQ : 0 < (P.reduceFst Q).ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (red c)) :=
        ord_pos_reduceFst_j P Q c hcQ

      have h2 := jValue_frobOnPlacesGeomLevel data hKr hFW
      rw [h1, hSnd] at h2
      have hac : red a = red c ^ q := jValue_unique hva h2

      have h3 := jValue_frobOnPlacesGeomLevel data hKr hva
      rw [← hQ.1] at h3
      have hca : red c = red a ^ q := jValue_unique hFQ h3
      have hfix : red a ^ (q ^ 2) = red a := by
        rw [sq, pow_mul, ← hca, ← hac]
      have hg1 := hgen.1
      rw [evalAt_jGeomGen_of_ord_pos hva] at hg1
      exact hg1 hfix
  ·
    rw [hSnd]; exact hQ.2

end S_ModularCurve_PlaceSpecialization_isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_isStrictSnd_and_reduceSnd_eq_of_ord_sub_pos (solution)
