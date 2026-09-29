-- Prove2me | solution 1 for IharaTower.RungAssembly.iharaClauseAt_rungDatumOfLegs
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c3452590-e76a-5975-97da-f7ab74b4c5b5

import Definitions.Def_HeckeModule_IharaRungDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_RungAssembly_iharaClauseAt_rungDatumOfLegs

set_option autoImplicit false

open IharaTower in

theorem solution
    {𝒪 : Type} [CommRing 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] {T' : Type} [CommRing T'] [Algebra 𝒪 T']
    {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}
    {n : ℕ} (L : RungAssembly.LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) (πT : T →ₐ[𝒪] 𝒪)
    (hequiv : ∀ (t' : T') (m : M),
      (RungAssembly.rungDatumOfLegs L c res).i (res t' • m)
        = t' • (RungAssembly.rungDatumOfLegs L c res).i m)
    (hsurj : ∀ w' ∈ (Submodule.torsionBySet T' M'
        ↑(RingHom.ker (πT.comp res))).restrictScalars 𝒪,
      ∃ m ∈ (Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪,
        (RungAssembly.rungDatumOfLegs L c res).i m = w') :
    IharaClauseAt (RungAssembly.rungDatumOfLegs L c res) πT (πT.comp res) := by
  show Submodule.map (RungAssembly.rungDatumOfLegs L c res).i
      ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪)
    = (Submodule.torsionBySet T' M' ↑(RingHom.ker (πT.comp res))).restrictScalars 𝒪
  refine le_antisymm ?_ ?_
  · intro w hw
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hw
    rw [Submodule.restrictScalars_mem, Submodule.mem_torsionBySet_iff]
    rintro ⟨t', ht'⟩
    have ht2 : πT (res t') = 0 := by
      have := (SetLike.mem_coe.mp ht')
      rwa [RingHom.mem_ker, AlgHom.comp_apply] at this
    have hzero : res t' • m = 0 := by
      rw [Submodule.restrictScalars_mem, Submodule.mem_torsionBySet_iff] at hm
      exact hm ⟨res t', SetLike.mem_coe.mpr (RingHom.mem_ker.mpr ht2)⟩
    calc (t' : T') • (RungAssembly.rungDatumOfLegs L c res).i m
        = (RungAssembly.rungDatumOfLegs L c res).i (res t' • m) := (hequiv t' m).symm
      _ = 0 := by rw [hzero]; exact map_zero _
  · intro w' hw'
    obtain ⟨m, hm, him⟩ := hsurj w' hw'
    exact Submodule.mem_map.mpr ⟨m, hm, him⟩

end S_IharaTower_RungAssembly_iharaClauseAt_rungDatumOfLegs
end P2MW
export P2MW.S_IharaTower_RungAssembly_iharaClauseAt_rungDatumOfLegs (solution)
