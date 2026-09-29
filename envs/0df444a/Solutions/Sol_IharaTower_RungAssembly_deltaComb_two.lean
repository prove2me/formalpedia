-- Prove2me | solution 1 for IharaTower.RungAssembly.deltaComb_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8d0b7518-5084-5e78-88b9-a63a55d8f766

import Mathlib
import Definitions.Def_HeckeModule_IharaRungDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_RungAssembly_deltaComb_two

set_option autoImplicit false

open IharaTower IharaTower.RungAssembly

theorem solution {𝒪 : Type} [CommRing 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] {T' : Type} [CommRing T'] [Algebra 𝒪 T']
    {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}
    (L : LegDatum (𝒪 := 𝒪) P P' 2) (t₀₀ t₀₁ t₁₀ t₁₁ : T) (htab : L.table = ![![t₀₀, t₀₁], ![t₁₀, t₁₁]]) (c : Fin 2 → T) :
    deltaComb L c = c 0 ^ 2 * t₀₀ + c 0 * c 1 * (t₀₁ + t₁₀) + c 1 ^ 2 * t₁₁ := by
  simp only [deltaComb, htab, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end S_IharaTower_RungAssembly_deltaComb_two
end P2MW
export P2MW.S_IharaTower_RungAssembly_deltaComb_two (solution)
