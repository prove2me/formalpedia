-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_expD_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:55:35.118195+00:00
-- url     : https://prove2.me/submissions/d18e5ff2-f382-449a-8550-fff3cce49847

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
import Theorems.Thm_GeneralPieces_GenF_der_multiset_prod
import Theorems.Thm_GeneralPieces_GenF_pderiv_expD


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
variable {Y A : Type} [CommRing A] [Algebra ℚ A]
namespace GeneralPieces.GenF
theorem _root_.solution {D : Y → Derivation ℚ A A} (hc : ∀ i j a, D i (D j a) = D j (D i a)) (i : Y) {ι : Type} [DecidableEq ι] (s : Multiset ι)
    (f g : ι → MvPowerSeries Y A) (hf : ∀ k, MvPowerSeries.pderiv A i (f k) + mapD (D i) (f k) = g k) (hg : ∀ k, expD D (g k) = g k) :
    MvPowerSeries.pderiv A i (expD D (s.map f).prod) = ∑ k ∈ s.toFinset, s.count k • (g k * expD D ((s.erase k).map f).prod) := by
  have h1 := der_multiset_prod ((MvPowerSeries.pderiv A i : MvPowerSeries Y A →ₗ[A] MvPowerSeries Y A).toAddMonoidHom)
    (fun a b => by
      show MvPowerSeries.pderiv A i (a * b) = a * MvPowerSeries.pderiv A i b + MvPowerSeries.pderiv A i a * b
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b]) s f
  have h2 := der_multiset_prod ((mapD (X := Y) (D i)).toAddMonoidHom) (fun a b => mapE_mul (isDer_derivation (D i)) a b) s f
  have h1' : MvPowerSeries.pderiv A i (s.map f).prod = ∑ k ∈ s.toFinset, s.count k • (MvPowerSeries.pderiv A i (f k) * ((s.erase k).map f).prod) := h1
  have h2' : mapD (D i) (s.map f).prod = ∑ k ∈ s.toFinset, s.count k • (mapD (D i) (f k) * ((s.erase k).map f).prod) := h2
  rw [pderiv_expD hc, ← map_add, h1', h2', ← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← nsmul_add, ← add_mul, hf, map_nsmul, map_mul, hg]
end GeneralPieces.GenF
