-- Prove2me | solution 1 for IharaTower.jDegL_smul_eq_res_smul_jDegL_of_generators_of_ordinary_refinement
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/45ddbcd3-2263-5862-ab25-d9555ecdc0ae

import Definitions.Def_CohCarrier_LevelPairing
import Mathlib.RingTheory.Noetherian.Defs
import Theorems.Thm_IharaTower_jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement
import Theorems.Thm_CohCarrier_jDeg_heckeT_comm_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_jDegL_smul_eq_res_smul_jDegL_of_generators_of_ordinary_refinement

set_option autoImplicit false

namespace CohL2
namespace ClauseD

open CohCarrier IharaLemma IharaTower IharaTower.CornerData CongruenceSubgroup
open scoped MatrixGroups

section Main

variable {N q : ℕ} [NeZero N] [NeZero q] [NeZero (N * q)]
    {Hs : Subgroup (ZMod N)ˣ} {Hs' : Subgroup (ZMod (N * q))ˣ}
    {𝒪 : Type} [CommRing 𝒪]
    {𝕋 𝕋₁ : Type} [CommRing 𝕋] [CommRing 𝕋₁] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋₁]
    [Module 𝕋 (H1 N Hs 𝒪)] [Module 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (H1 N Hs 𝒪)] [IsScalarTower 𝒪 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs 𝒪 𝕋) (cd₁ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋₁)

theorem res_equivariance_of_adjoin
    (j : H1 (N * q) Hs' 𝒪 →ₗ[𝒪] H1 N Hs 𝒪)
    (hj : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx) →
      j v' ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx))
    (res : cd₁.cornerRing →ₐ[𝒪] cd.cornerRing)
    (G : Set cd₁.cornerRing) (hG : Algebra.adjoin 𝒪 G = ⊤)
    (hgen : ∀ x ∈ G, ∀ (m' : cd₁.cornerModule) (jm jtm : cd.cornerModule),
      (jm : H1 N Hs 𝒪) = j (m' : H1 (N * q) Hs' 𝒪) →
      (jtm : H1 N Hs 𝒪) = j ((x • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) → jtm = res x • jm) :
    ∀ (t : cd₁.cornerRing) (m' : cd₁.cornerModule) (jm jtm : cd.cornerModule),
      (jm : H1 N Hs 𝒪) = j (m' : H1 (N * q) Hs' 𝒪) →
      (jtm : H1 N Hs 𝒪) = j ((t • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) → jtm = res t • jm := by
  intro t
  have ht : t ∈ Algebra.adjoin 𝒪 G := hG ▸ Algebra.mem_top
  refine Algebra.adjoin_induction (p := fun s _ => ∀ (m' : cd₁.cornerModule) (jm jtm : cd.cornerModule),
      (jm : H1 N Hs 𝒪) = j (m' : H1 (N * q) Hs' 𝒪) →
      (jtm : H1 N Hs 𝒪) = j ((s • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) → jtm = res s • jm)
    ?_ ?_ ?_ ?_ ht
  · exact hgen
  · intro r m' jm jtm hjm hjtm
    apply Subtype.ext
    rw [AlgHom.commutes, algebraMap_smul, Submodule.coe_smul_of_tower, hjtm, hjm, algebraMap_smul,
      Submodule.coe_smul_of_tower, map_smul]
  · intro x y _ _ hx hy m' jm jtm hjm hjtm
    have hxm : j ((x • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) ∈
        cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx) := hj _ (x • m').2
    have hym : j ((y • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) ∈
        cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx) := hj _ (y • m').2
    have ex := hx m' jm ⟨_, hxm⟩ hjm rfl
    have ey := hy m' jm ⟨_, hym⟩ hjm rfl
    apply Subtype.ext
    rw [map_add, add_smul, Submodule.coe_add, ← ex, ← ey, hjtm, add_smul, Submodule.coe_add, map_add]
  · intro x y _ _ hx hy m' jm jtm hjm hjtm
    have hym : j ((y • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) ∈
        cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx) := hj _ (y • m').2
    have ey := hy m' jm ⟨_, hym⟩ hjm rfl
    have ex := hx (y • m') ⟨_, hym⟩ jtm rfl (by rw [hjtm, show (x * y) • m' = x • y • m' from mul_smul x y m'])
    rw [ex, ey, ← show (res x * res y) • jm = res x • res y • jm from mul_smul (res x) (res y) jm, ← map_mul]

end Main

section Assembly

variable {N q : ℕ} [NeZero N] [NeZero q] [NeZero (N * q)]
    {Hs : Subgroup (ZMod N)ˣ} {Hs' : Subgroup (ZMod (N * q))ˣ}
    (h1 : LevelLE N (N * q) Hs Hs' 1) (hq' : LevelLE N (N * q) Hs Hs' q)
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] [IsLocalRing 𝒪]
    {𝕋 𝕋ₐ 𝕋₁ : Type} [CommRing 𝕋] [CommRing 𝕋ₐ] [CommRing 𝕋₁] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋ₐ] [Algebra 𝒪 𝕋₁]
    [Module 𝕋 (H1 N Hs 𝒪)] [Module 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [Module 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (H1 N Hs 𝒪)] [IsScalarTower 𝒪 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [IsScalarTower 𝒪 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs 𝒪 𝕋) (cdₐ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋ₐ)
    (cd₁ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋₁)

theorem clause_d
    (hincl : ∀ v : H1 (N * q) Hs' 𝒪, v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx) →
      v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx))
    (hstab : ∀ (t : 𝕋₁) (v : H1 (N * q) Hs' 𝒪),
      v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      t • v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx))
    (mjq : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v' ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx))
    (mj1 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v' ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx))
    (U : 𝕋₁) (hUact : ∀ v' : H1 (N * q) Hs' 𝒪, U • v' = heckeT (N * q) Hs' q 𝒪 v')
    (tp αt : cd.cornerRing)
    (hquad : αt * αt - tp * αt + algebraMap 𝒪 cd.cornerRing (q : 𝒪) = 0)
    (hTp : ∀ m : cd.cornerModule, ((tp • m : cd.cornerModule) : H1 N Hs 𝒪) = heckeT N Hs q 𝒪 (m : H1 N Hs 𝒪))
    (R1 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (heckeT (N * q) Hs' q 𝒪 v') = q • jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v')
    (R2 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (heckeT (N * q) Hs' q 𝒪 v') =
        heckeT N Hs q 𝒪 (jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v') - jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v')
    [Module.Finite 𝒪 cd.cornerModule] [Module.Finite 𝒪 cd.cornerRing]
    (hUunit : U ∉ cd₁.split.𝔪 cd₁.idx)
    (hβmem : tp - αt ∈ IsLocalRing.maximalIdeal cd.cornerRing)
    (res : cd₁.cornerRing →ₐ[𝒪] cd.cornerRing)
    (hresU : res (cd₁.split.toCornerRing cd₁.idx U) = αt)
    (G : Set cd₁.cornerRing) (hG : Algebra.adjoin 𝒪 G = ⊤)
    (hgen : ∀ x ∈ G,
      (∃ (A' : H1 (N * q) Hs' 𝒪 → H1 (N * q) Hs' 𝒪) (A : H1 N Hs 𝒪 → H1 N Hs 𝒪),
        (∀ m : cd₁.cornerModule, ((x • m : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) =
          A' (m : H1 (N * q) Hs' 𝒪)) ∧
        (∀ m : cd.cornerModule, ((res x • m : cd.cornerModule) : H1 N Hs 𝒪) = A (m : H1 N Hs 𝒪)) ∧
        (∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx) →
          jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (A' v') = A (jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v')) ∧
        (∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx) →
          jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (A' v') = A (jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v'))) ∨
      x = cd₁.split.toCornerRing cd₁.idx U) :
    (∀ (t₁ : cd₁.cornerRing) (m' : cd₁.cornerModule) (jm jtm : cd.cornerModule),
      (jm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (m' : H1 (N * q) Hs' 𝒪) →
      (jtm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' ((t₁ • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) →
      jtm = res t₁ • jm) ∧
    (∀ (t₁ : cd₁.cornerRing) (m' : cd₁.cornerModule) (jm jtm : cd.cornerModule),
      (jm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (m' : H1 (N * q) Hs' 𝒪) →
      (jtm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 ((t₁ • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) →
      jtm = res t₁ • jm) := by

  have hUx : ∀ m' : cd₁.cornerModule,
      ((cd₁.split.toCornerRing cd₁.idx U • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) =
        heckeT (N * q) Hs' q 𝒪 (m' : H1 (N * q) Hs' 𝒪) := by
    intro m'
    rw [IdempotentSplitting.coe_cornerSmul, IdempotentSplitting.coe_toCornerRing, mul_smul, mul_smul,
      cd₁.split.e_smul_coe cd₁.idx m', ← hUact]
    exact cd₁.split.e_smul_coe cd₁.idx ⟨U • (m' : H1 (N * q) Hs' 𝒪), Submodule.smul_mem _ U m'.2⟩
  have key := fun (m' : cd₁.cornerModule) (jmq jm1 : cd.cornerModule) hjmq hjm1 =>
    IharaTower.jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement h1 hq' cd cdₐ cd₁ hstab mjq mj1 U hUact tp αt hquad hTp R1 R2
      hUunit hβmem (m' : H1 (N * q) Hs' 𝒪) (hincl _ m'.2) m'.2 jmq jm1 hjmq hjm1
  constructor
  · refine res_equivariance_of_adjoin cd cd₁ (jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq')
      (fun v' hv' => mjq v' (hincl v' hv')) res G hG ?_
    intro x hx m' jm jtm hjm hjtm
    rcases hgen x hx with ⟨A', A, hup, hdown, hcq, -⟩ | rfl
    · apply Subtype.ext
      rw [hdown, hjm, hjtm, hup, hcq _ m'.2]
    · have hm1 : jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (m' : H1 (N * q) Hs' 𝒪) ∈
          cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx) := mj1 _ (hincl _ m'.2)
      obtain ⟨hA, -⟩ := key m' jm ⟨_, hm1⟩ hjm rfl
      apply Subtype.ext
      rw [hjtm, hUx, hA, hresU]
  · refine res_equivariance_of_adjoin cd cd₁ (jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1)
      (fun v' hv' => mj1 v' (hincl v' hv')) res G hG ?_
    intro x hx m' jm jtm hjm hjtm
    rcases hgen x hx with ⟨A', A, hup, hdown, -, hc1⟩ | rfl
    · apply Subtype.ext
      rw [hdown, hjm, hjtm, hup, hc1 _ m'.2]
    · have hmq : jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (m' : H1 (N * q) Hs' 𝒪) ∈
          cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx) := mjq _ (hincl _ m'.2)
      obtain ⟨-, hB⟩ := key m' ⟨_, hmq⟩ jm rfl hjm
      apply Subtype.ext
      rw [hjtm, hUx, hB, hresU]

end Assembly

end CohL2.ClauseD

open CohCarrier IharaLemma IharaTower in
theorem solution
    {N q : ℕ} [NeZero N] [NeZero q] [NeZero (N * q)]
    {Hs : Subgroup (ZMod N)ˣ} {Hs' : Subgroup (ZMod (N * q))ˣ}
    (h1 : LevelLE N (N * q) Hs Hs' 1) (hq' : LevelLE N (N * q) Hs Hs' q)
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] [IsLocalRing 𝒪]
    {𝕋 𝕋ₐ 𝕋₁ : Type} [CommRing 𝕋] [CommRing 𝕋ₐ] [CommRing 𝕋₁] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋ₐ] [Algebra 𝒪 𝕋₁]
    [Module 𝕋 (H1 N Hs 𝒪)] [Module 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [Module 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (H1 N Hs 𝒪)] [IsScalarTower 𝒪 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [IsScalarTower 𝒪 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs 𝒪 𝕋) (cdₐ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋ₐ)
    (cd₁ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋₁)
    (hincl : ∀ v : H1 (N * q) Hs' 𝒪, v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx) →
      v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx))
    (hstab : ∀ (t : 𝕋₁) (v : H1 (N * q) Hs' 𝒪),
      v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      t • v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx))
    (mjq : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v' ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx))
    (mj1 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v' ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx))
    (U : 𝕋₁) (hUact : ∀ v' : H1 (N * q) Hs' 𝒪, U • v' = heckeT (N * q) Hs' q 𝒪 v')
    (tp αt : cd.cornerRing)
    (hquad : αt * αt - tp * αt + algebraMap 𝒪 cd.cornerRing (q : 𝒪) = 0)
    (hTp : ∀ m : cd.cornerModule, ((tp • m : cd.cornerModule) : H1 N Hs 𝒪) = heckeT N Hs q 𝒪 (m : H1 N Hs 𝒪))
    (R1 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (heckeT (N * q) Hs' q 𝒪 v') = q • jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v')
    (R2 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (heckeT (N * q) Hs' q 𝒪 v') =
        heckeT N Hs q 𝒪 (jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v') - jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v')
    [Module.Finite 𝒪 cd.cornerModule] [Module.Finite 𝒪 cd.cornerRing]
    (hUunit : U ∉ cd₁.split.𝔪 cd₁.idx)
    (hβmem : tp - αt ∈ IsLocalRing.maximalIdeal cd.cornerRing)
    (res : cd₁.cornerRing →ₐ[𝒪] cd.cornerRing)
    (hresU : res (cd₁.split.toCornerRing cd₁.idx U) = αt)
    (G : Set cd₁.cornerRing) (hG : Algebra.adjoin 𝒪 G = ⊤)
    (hgen : ∀ x ∈ G,
      (∃ (A' : H1 (N * q) Hs' 𝒪 → H1 (N * q) Hs' 𝒪) (A : H1 N Hs 𝒪 → H1 N Hs 𝒪),
        (∀ m : cd₁.cornerModule, ((x • m : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) =
          A' (m : H1 (N * q) Hs' 𝒪)) ∧
        (∀ m : cd.cornerModule, ((res x • m : cd.cornerModule) : H1 N Hs 𝒪) = A (m : H1 N Hs 𝒪)) ∧
        (∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx) →
          jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (A' v') = A (jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v')) ∧
        (∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx) →
          jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (A' v') = A (jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v'))) ∨
      x = cd₁.split.toCornerRing cd₁.idx U) :
    (∀ (t₁ : cd₁.cornerRing) (m' : cd₁.cornerModule) (jm jtm : cd.cornerModule),
      (jm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (m' : H1 (N * q) Hs' 𝒪) →
      (jtm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' ((t₁ • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) →
      jtm = res t₁ • jm) ∧
    (∀ (t₁ : cd₁.cornerRing) (m' : cd₁.cornerModule) (jm jtm : cd.cornerModule),
      (jm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (m' : H1 (N * q) Hs' 𝒪) →
      (jtm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 ((t₁ • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) →
      jtm = res t₁ • jm) :=
  CohL2.ClauseD.clause_d h1 hq' cd cdₐ cd₁ hincl hstab mjq mj1 U hUact tp αt hquad hTp R1 R2 hUunit hβmem res hresU G hG hgen

end S_IharaTower_jDegL_smul_eq_res_smul_jDegL_of_generators_of_ordinary_refinement
end P2MW
export P2MW.S_IharaTower_jDegL_smul_eq_res_smul_jDegL_of_generators_of_ordinary_refinement (solution)
