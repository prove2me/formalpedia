-- Prove2me | solution 1 for LT.LatticeTree.eq_of_le_of_hasDetIndex_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3b9ee218-43ec-521e-a955-167f7fa8f230

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_eq_of_le_of_hasDetIndex_padic

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega LT.LatticeTree

open scoped PadicInt Padic

namespace B28QBCA
open LT.LatticeTree

theorem isInteger_entries_of_latticeMap_le (p : ℕ) [Fact p.Prime]
    (h : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
    (hle : latticeMap h (stdLattice ℤ_[p] ℚ_[p]) ≤ stdLattice ℤ_[p] ℚ_[p]) (i j : Fin 2) :
    IsLocalization.IsInteger ℤ_[p] ((h : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j) := by
  have hmem : (Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) ℚ_[p]) (Pi.single j 1 : Fin 2 → ℚ_[p])) ∈ stdLattice ℤ_[p] ℚ_[p] :=
    hle (mulVec_mem_latticeMap (single_one_mem_stdLattice ℤ_[p] ℚ_[p] j))
  have := (mem_stdLattice ℤ_[p] ℚ_[p]).mp hmem i
  rwa [Matrix.mulVec_single_one] at this

end B28QBCA

open B28QBCA in
theorem solution
    (p : ℕ) [Fact p.Prime] (N N' : Submodule ℤ_[p] (Fin 2 → ℚ_[p])) (hle : N ≤ N') (e : ℤ)
    (hN : HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) N e) (hN' : HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) N' e) :
    N = N' := by
  classical
  obtain ⟨g, hg, u, hu⟩ := hN
  obtain ⟨g', hg', u', hu'⟩ := hN'
  set h : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p] := g'⁻¹ * g with hh

  have hhle : latticeMap h (stdLattice ℤ_[p] ℚ_[p]) ≤ stdLattice ℤ_[p] ℚ_[p] := by
    have := latticeMap_mono g'⁻¹ (hg.symm ▸ hg'.symm ▸ hle : latticeMap g (stdLattice ℤ_[p] ℚ_[p]) ≤
      latticeMap g' (stdLattice ℤ_[p] ℚ_[p]))
    rwa [latticeMap_inv_latticeMap, ← latticeMap_mul] at this

  have hint := isInteger_entries_of_latticeMap_le p h hhle
  choose h₀f hh₀f using hint
  set h₀ : Matrix (Fin 2) (Fin 2) ℤ_[p] := Matrix.of h₀f with hh₀
  have hmap : h₀.map (algebraMap ℤ_[p] ℚ_[p]) = (h : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    ext i j
    simp only [Matrix.map_apply, hh₀, Matrix.of_apply]
    exact hh₀f i j

  have hp0 : (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) ≠ 0 := by
    rw [map_natCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hdet : algebraMap ℤ_[p] ℚ_[p] h₀.det = algebraMap ℤ_[p] ℚ_[p] (u * u'⁻¹ : ℤ_[p]ˣ) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
    have e1 : ((h : Matrix (Fin 2) (Fin 2) ℚ_[p])).det =
        ((Matrix.GeneralLinearGroup.det g : ℚ_[p]ˣ) : ℚ_[p]) *
          (((Matrix.GeneralLinearGroup.det g' : ℚ_[p]ˣ) : ℚ_[p]))⁻¹ := by
      rw [hh, Units.val_mul, Matrix.det_mul, Matrix.coe_units_inv, Matrix.det_nonsing_inv,
        Ring.inverse_eq_inv', mul_comm]
      rfl
    rw [e1, hu, hu', Units.val_mul, map_mul, map_units_inv]
    have hu'0 : algebraMap ℤ_[p] ℚ_[p] (u' : ℤ_[p]) ≠ 0 :=
      (IsFractionRing.injective ℤ_[p] ℚ_[p]).ne_iff.mpr (Units.ne_zero u') |>.trans_eq (map_zero _) |> fun h => by
        intro h0; exact (Units.ne_zero u') ((IsFractionRing.injective ℤ_[p] ℚ_[p]) (h0.trans (map_zero _).symm))
    have hpe : (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) ^ e ≠ 0 := zpow_ne_zero e hp0
    field_simp
  have hdetu : IsUnit h₀.det := by
    have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := IsFractionRing.injective ℤ_[p] ℚ_[p]
    rw [hinj hdet]
    exact Units.isUnit _

  have hrange : h ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p])).range := by
    obtain ⟨hu0, hhu0⟩ := (Matrix.isUnit_iff_isUnit_det h₀).mpr hdetu
    refine ⟨hu0, ?_⟩
    apply Units.ext
    rw [← hmap, ← hhu0]
    rfl
  have hfix : latticeMap h (stdLattice ℤ_[p] ℚ_[p]) = stdLattice ℤ_[p] ℚ_[p] :=
    (latticeMap_stdLattice_eq_iff_mem_range h).mpr hrange
  calc N = latticeMap g (stdLattice ℤ_[p] ℚ_[p]) := hg.symm
    _ = latticeMap (g' * h) (stdLattice ℤ_[p] ℚ_[p]) := by rw [hh, mul_inv_cancel_left]
    _ = latticeMap g' (latticeMap h (stdLattice ℤ_[p] ℚ_[p])) := latticeMap_mul _ _ _
    _ = N' := by rw [hfix, hg']

end S_LT_LatticeTree_eq_of_le_of_hasDetIndex_padic
end P2MW
export P2MW.S_LT_LatticeTree_eq_of_le_of_hasDetIndex_padic (solution)
