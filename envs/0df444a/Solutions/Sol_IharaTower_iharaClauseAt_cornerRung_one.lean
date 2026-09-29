-- Prove2me | solution 1 for IharaTower.iharaClauseAt_cornerRung_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/569f85fa-627e-5b69-b991-45ffcbb23bba

import Mathlib
import Definitions.Def_HeckeModule_IharaDataAt
import Theorems.Thm_IharaTower_iharaClauseAt_and_isIharaDataAt_cornerRung
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_iharaClauseAt_cornerRung_one

set_option autoImplicit false

open IharaLemma IharaTower IharaTower.RungAssembly in

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {V V' : Type} [AddCommGroup V] [Module 𝒪 V] [AddCommGroup V'] [Module 𝒪 V']
    {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
    [Module 𝕋 V] [Module 𝕋' V'] [IsScalarTower 𝒪 𝕋 V] [IsScalarTower 𝒪 𝕋' V']
    (S : IdempotentSplitting 𝕋) (S' : IdempotentSplitting 𝕋') (i₀ : Fin S.n) (i₀' : Fin S'.n)
    (P : IharaTower.LevelPairing (𝒪 := 𝒪) (S.CornerRing i₀) ↥(cornerSubmodule (M := V) (S.e i₀)))
    (P' : IharaTower.LevelPairing (𝒪 := 𝒪) (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀')))
    (iα : ↥(cornerSubmodule (M := V) (S.e i₀)) →ₗ[𝒪] ↥(cornerSubmodule (M := V') (S'.e i₀')))
    (jα : ↥(cornerSubmodule (M := V') (S'.e i₀')) →ₗ[𝒪] ↥(cornerSubmodule (M := V) (S.e i₀)))
    (Δ₀ : S.CornerRing i₀)
    (hadj : ∀ (m' : ↥(cornerSubmodule (M := V') (S'.e i₀'))) (m : ↥(cornerSubmodule (M := V) (S.e i₀))),
      P.B (jα m') m = P'.B m' (iα m))
    (hji : ∀ m : ↥(cornerSubmodule (M := V) (S.e i₀)), jα (iα m) = Δ₀ • m)
    (res : S'.CornerRing i₀' →ₐ[𝒪] S.CornerRing i₀) (πT : S.CornerRing i₀ →ₐ[𝒪] 𝒪)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := V) (S.e i₀))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := V) (S.e i₀))]
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := V') (S'.e i₀'))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := V') (S'.e i₀'))]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : ↥(cornerSubmodule (M := V) (S.e i₀))) (x : ↥(cornerSubmodule (M := V') (S'.e i₀'))),
      iα v = ϖ • x → ∃ v₁, v = ϖ • v₁)
    (hjeq : ∀ (t' : S'.CornerRing i₀') (m' : ↥(cornerSubmodule (M := V') (S'.e i₀'))), jα (t' • m') = res t' • jα m')
    (hsat' : ∀ (a : 𝒪) (m' : ↥(cornerSubmodule (M := V') (S'.e i₀'))), a ≠ 0 →
      a • m' ∈ (RingHom.ker (πT.comp res) • ⊤ :
        Submodule (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))).restrictScalars 𝒪 →
      m' ∈ (RingHom.ker (πT.comp res) • ⊤ :
        Submodule (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))).restrictScalars 𝒪)
    (hrank : Module.finrank 𝒪
        ((Submodule.torsionBySet (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))
          ↑(RingHom.ker (πT.comp res))).restrictScalars 𝒪)
      ≤ Module.finrank 𝒪
        ((Submodule.torsionBySet (S.CornerRing i₀) ↥(cornerSubmodule (M := V) (S.e i₀))
          ↑(RingHom.ker πT)).restrictScalars 𝒪)) :
    Submodule.map iα ((Submodule.torsionBySet (S.CornerRing i₀) ↥(cornerSubmodule (M := V) (S.e i₀))
        ↑(RingHom.ker πT)).restrictScalars 𝒪) =
      (Submodule.torsionBySet (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))
        ↑(RingHom.ker (πT.comp res))).restrictScalars 𝒪 ∧
    ∃ L : LegDatum (T := S.CornerRing i₀) (T' := S'.CornerRing i₀')
        (M := ↥(cornerSubmodule (M := V) (S.e i₀))) (M' := ↥(cornerSubmodule (M := V') (S'.e i₀'))) (𝒪 := 𝒪) P P' 1,
      L.iLeg = ![iα] ∧ L.jLeg = ![jα] ∧ L.table = ![![Δ₀]] ∧
      IharaTower.IharaClauseAt (IharaTower.cornerRung S S' i₀ i₀' P P' L ![1] res) πT (πT.comp res) ∧
      IharaTower.IsIharaDataAt (IharaTower.cornerRung S S' i₀ i₀' P P' L ![1] res) πT (πT.comp res) := by
  let L : LegDatum (T := S.CornerRing i₀) (T' := S'.CornerRing i₀')
      (M := ↥(cornerSubmodule (M := V) (S.e i₀))) (M' := ↥(cornerSubmodule (M := V') (S'.e i₀'))) (𝒪 := 𝒪) P P' 1 :=
    ⟨![iα], ![jα], fun k m' m => by fin_cases k; exact hadj m' m, ![![Δ₀]],
      fun k k' m => by fin_cases k; fin_cases k'; simpa using hji m⟩
  have hiComb : ∀ v, iComb L ![1] v = iα v := fun v => by
    simp [iComb, L]
  have hjComb : ∀ m', jComb L ![1] m' = jα m' := fun m' => by
    simp [jComb, L]
  have key := IharaTower.iharaClauseAt_and_isIharaDataAt_cornerRung S S' i₀ i₀' P P' L ![1] res πT hϖ
    (fun v x h => hres v x (by rwa [hiComb] at h))
    (fun t' m' => by rw [hjComb, hjComb, hjeq]) hsat' hrank
  refine ⟨?_, L, rfl, rfl, rfl, key.1, key.2⟩
  have h1 := key.1
  rw [IharaTower.IharaClauseAt, IharaTower.cornerRung_i] at h1
  have hext : iComb L ![1] = iα := LinearMap.ext hiComb
  rwa [hext] at h1

end S_IharaTower_iharaClauseAt_cornerRung_one
end P2MW
export P2MW.S_IharaTower_iharaClauseAt_cornerRung_one (solution)
