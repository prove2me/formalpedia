-- Prove2me | solution 1 for IharaTower.jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f4fb9d6a-e5af-5f8b-bbcf-117451e4a6ae

import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.Tactic.Module
import Definitions.Def_CohCarrier_LevelPairing
import Theorems.Thm_IharaLemma_eq_zero_of_mem_cornerSubmodule_of_intertwining_nilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement

set_option autoImplicit false

namespace CohL2
namespace DCore

open IsLocalRing IharaLemma

theorem exists_pow_mem_map_pow {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R]
    (x : R) (hx : x ∈ maximalIdeal R) (k : ℕ) :
    ∃ n : ℕ, x ^ n ∈ (maximalIdeal 𝒪 ^ k).map (algebraMap 𝒪 R) := by
  set I : Ideal R := (maximalIdeal 𝒪).map (algebraMap 𝒪 R) with hI
  haveI : Module.Finite 𝒪 (R ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 I).toLinearMap (Ideal.Quotient.mkₐ_surjective 𝒪 I)
  haveI : IsArtinianRing (𝒪 ⧸ maximalIdeal 𝒪) := inferInstanceAs (IsArtinianRing (ResidueField 𝒪))
  haveI : Module.Finite (𝒪 ⧸ maximalIdeal 𝒪) (R ⧸ I) :=
    Module.Finite.of_restrictScalars_finite 𝒪 (𝒪 ⧸ maximalIdeal 𝒪) (R ⧸ I)
  haveI : IsArtinianRing (R ⧸ I) := IsArtinianRing.of_finite (𝒪 ⧸ maximalIdeal 𝒪) (R ⧸ I)
  obtain ⟨N, hN⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  refine ⟨N * k, ?_⟩
  rw [pow_mul, Ideal.map_pow]
  exact Ideal.pow_mem_pow (hN (Ideal.pow_mem_pow hx N)) k

theorem smul_mem_of_mem_map {𝒪 : Type} [CommRing 𝒪] {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Module 𝒪 M] [IsScalarTower 𝒪 R M]
    (J : Ideal 𝒪) (y : R) (hy : y ∈ J.map (algebraMap 𝒪 R)) (m : M) :
    y • m ∈ (J • ⊤ : Submodule 𝒪 M) := by
  revert m
  refine Submodule.span_induction (p := fun y _ => ∀ m : M, y • m ∈ (J • ⊤ : Submodule 𝒪 M)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨a, ha, rfl⟩ m
    rw [algebraMap_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · intro m; rw [zero_smul]; exact Submodule.zero_mem _
  · intro y z _ _ hy hz m; rw [add_smul]; exact Submodule.add_mem _ (hy m) (hz m)
  · intro r y _ hy m
    rw [smul_eq_mul, mul_comm, mul_smul]
    exact hy (r • m)

theorem nilpotent_smul {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Module 𝒪 M] [IsScalarTower 𝒪 R M]
    (x : R) (hx : x ∈ maximalIdeal R) (k : ℕ) :
    ∃ n : ℕ, ∀ m : M, ((x • (LinearMap.id : M →ₗ[𝒪] M)) ^ n) m ∈ (maximalIdeal 𝒪 ^ k • ⊤ : Submodule 𝒪 M) := by
  have hpow : ∀ (n : ℕ) (m : M), ((x • (LinearMap.id : M →ₗ[𝒪] M)) ^ n) m = (x ^ n) • m := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ n ih =>
      intro m
      rw [pow_succ, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, ih, smul_smul, ← pow_succ]
  obtain ⟨n, hn⟩ := exists_pow_mem_map_pow (𝒪 := 𝒪) x hx k
  refine ⟨n, fun m => ?_⟩
  rw [hpow]
  exact smul_mem_of_mem_map _ _ hn m

end CohL2.DCore

namespace CohL2
namespace DCore

open CohCarrier IharaLemma IharaTower IharaTower.CornerData CongruenceSubgroup
open scoped MatrixGroups

section Main

variable {N q : ℕ} [NeZero N] [NeZero q] [NeZero (N * q)]
    {Hs : Subgroup (ZMod N)ˣ} {Hs' : Subgroup (ZMod (N * q))ˣ}
    (h1 : LevelLE N (N * q) Hs Hs' 1) (hq' : LevelLE N (N * q) Hs Hs' q)
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] [IsLocalRing 𝒪]
    {𝕋 𝕋ₐ 𝕋₁ : Type} [CommRing 𝕋] [CommRing 𝕋ₐ] [CommRing 𝕋₁] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋ₐ] [Algebra 𝒪 𝕋₁]
    [Module 𝕋 (H1 N Hs 𝒪)] [Module 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [Module 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (H1 N Hs 𝒪)] [IsScalarTower 𝒪 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [IsScalarTower 𝒪 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs 𝒪 𝕋) (cdₐ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋ₐ)
    (cd₁ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋₁)

def Ua (hstab : ∀ (t : 𝕋₁) (v : H1 (N * q) Hs' 𝒪),
      v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      t • v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx)) :
    Submodule 𝕋₁ (H1 (N * q) Hs' 𝒪) where
  carrier := cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx)
  add_mem' ha hb := Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  smul_mem' t v hv := hstab t v hv

variable (hstab : ∀ (t : 𝕋₁) (v : H1 (N * q) Hs' 𝒪),
      v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      t • v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx))
    (mjq : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v' ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx))
    (mj1 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v' ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx))

noncomputable def Jq : ↥(Ua cdₐ hstab) →ₗ[𝒪] cd.cornerModule where
  toFun v := ⟨jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (v : H1 (N * q) Hs' 𝒪), mjq _ v.2⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (by simp)

noncomputable def J1 : ↥(Ua cdₐ hstab) →ₗ[𝒪] cd.cornerModule where
  toFun v := ⟨jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (v : H1 (N * q) Hs' 𝒪), mj1 _ v.2⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (by simp)

@[scoped simp] theorem coe_Jq (v : ↥(Ua cdₐ hstab)) :
    ((Jq hq' cd cdₐ hstab mjq v : cd.cornerModule) : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (v : H1 (N * q) Hs' 𝒪) := rfl

@[scoped simp] theorem coe_J1 (v : ↥(Ua cdₐ hstab)) :
    ((J1 h1 cd cdₐ hstab mj1 v : cd.cornerModule) : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (v : H1 (N * q) Hs' 𝒪) := rfl

variable (U : 𝕋₁) (hUact : ∀ v' : H1 (N * q) Hs' 𝒪, U • v' = heckeT (N * q) Hs' q 𝒪 v')
    (tp αt : cd.cornerRing)
    (hquad : αt * αt - tp * αt + algebraMap 𝒪 cd.cornerRing (q : 𝒪) = 0)
    (hTp : ∀ m : cd.cornerModule, ((tp • m : cd.cornerModule) : H1 N Hs 𝒪) = heckeT N Hs q 𝒪 (m : H1 N Hs 𝒪))
    (R1 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (heckeT (N * q) Hs' q 𝒪 v') = q • jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v')
    (R2 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (heckeT (N * q) Hs' q 𝒪 v') =
        heckeT N Hs q 𝒪 (jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v') - jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v')

include hUact in
theorem coe_U_smul (v : ↥(Ua cdₐ hstab)) :
    ((U • v : ↥(Ua cdₐ hstab)) : H1 (N * q) Hs' 𝒪) = heckeT (N * q) Hs' q 𝒪 (v : H1 (N * q) Hs' 𝒪) := by
  rw [Submodule.coe_smul, hUact]

include hUact hTp R1 R2 in

theorem J_U (v : ↥(Ua cdₐ hstab)) :
    J1 h1 cd cdₐ hstab mj1 (U • v) = algebraMap 𝒪 cd.cornerRing (q : 𝒪) • Jq hq' cd cdₐ hstab mjq v ∧
    Jq hq' cd cdₐ hstab mjq (U • v) = tp • Jq hq' cd cdₐ hstab mjq v - J1 h1 cd cdₐ hstab mj1 v := by
  have hc := coe_U_smul cdₐ hstab U hUact v
  constructor
  · apply Subtype.ext
    rw [algebraMap_smul]
    show jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 ((U • v : ↥(Ua cdₐ hstab)) : H1 (N * q) Hs' 𝒪) =
      ((((q : 𝒪) • Jq hq' cd cdₐ hstab mjq v : cd.cornerModule)) : H1 N Hs 𝒪)
    rw [hc, R1 _ v.2, Submodule.coe_smul_of_tower, coe_Jq, Nat.cast_smul_eq_nsmul]
  · apply Subtype.ext
    show jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' ((U • v : ↥(Ua cdₐ hstab)) : H1 (N * q) Hs' 𝒪) =
      (((tp • Jq hq' cd cdₐ hstab mjq v - J1 h1 cd cdₐ hstab mj1 v : cd.cornerModule)) : H1 N Hs 𝒪)
    rw [hc, R2 _ v.2, Submodule.coe_sub, hTp, coe_Jq, coe_J1]

include hUact hTp R1 R2 hquad in

theorem intertwine (v : ↥(Ua cdₐ hstab)) :
    (J1 h1 cd cdₐ hstab mj1 - (tp - αt) • Jq hq' cd cdₐ hstab mjq) (U • v) =
      ((tp - αt) • (LinearMap.id : cd.cornerModule →ₗ[𝒪] cd.cornerModule))
        ((J1 h1 cd cdₐ hstab mj1 - (tp - αt) • Jq hq' cd cdₐ hstab mjq) v) := by
  obtain ⟨hA, hB⟩ := J_U h1 hq' cd cdₐ hstab mjq mj1 U hUact tp hTp R1 R2 v
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hA, hB]
  have hβ2 : (tp - αt) * (tp - αt) = (tp - αt) * tp - algebraMap 𝒪 cd.cornerRing (q : 𝒪) := by
    linear_combination hquad
  simp only [smul_sub, smul_smul]
  rw [hβ2]
  module

variable [Module.Finite 𝒪 cd.cornerModule] [Module.Finite 𝒪 cd.cornerRing]
    (hUunit : U ∉ cd₁.split.𝔪 cd₁.idx)
    (hβmem : tp - αt ∈ IsLocalRing.maximalIdeal cd.cornerRing)

include hUact hTp R1 R2 hquad hUunit hβmem in

theorem J1_eq (v : ↥(Ua cdₐ hstab))
    (hv : (v : H1 (N * q) Hs' 𝒪) ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx)) :
    J1 h1 cd cdₐ hstab mj1 v = (tp - αt) • Jq hq' cd cdₐ hstab mjq v := by
  have hsep : ∀ m : cd.cornerModule,
      (∀ k : ℕ, m ∈ (IsLocalRing.maximalIdeal 𝒪 ^ k • ⊤ : Submodule 𝒪 cd.cornerModule)) → m = 0 := by
    intro m hm
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := cd.cornerModule)
      (I := IsLocalRing.maximalIdeal 𝒪) (IsLocalRing.maximalIdeal.isMaximal 𝒪).ne_top
    have : m ∈ (⨅ i : ℕ, IsLocalRing.maximalIdeal 𝒪 ^ i • ⊤ : Submodule 𝒪 cd.cornerModule) :=
      Submodule.mem_iInf _ |>.mpr hm
    rw [hK, Submodule.mem_bot] at this
    exact this
  have key := IharaLemma.eq_zero_of_mem_cornerSubmodule_of_intertwining_nilpotent
    (J1 h1 cd cdₐ hstab mj1 - (tp - αt) • Jq hq' cd cdₐ hstab mjq) cd₁.split cd₁.idx U hUunit
    ((tp - αt) • (LinearMap.id : cd.cornerModule →ₗ[𝒪] cd.cornerModule))
    (intertwine h1 hq' cd cdₐ hstab mjq mj1 U hUact tp αt hquad hTp R1 R2)
    (IsLocalRing.maximalIdeal 𝒪)
    (fun k => nilpotent_smul (𝒪 := 𝒪) (R := cd.cornerRing) (M := cd.cornerModule) (tp - αt) hβmem k) hsep
  have hmem : v ∈ cornerSubmodule (M := ↥(Ua cdₐ hstab)) (cd₁.split.e cd₁.idx) := by
    refine ⟨v, Subtype.ext ?_⟩
    obtain ⟨y, hy⟩ := hv
    show cd₁.split.e cd₁.idx • (v : H1 (N * q) Hs' 𝒪) = v
    have hy' : cd₁.split.e cd₁.idx • y = (v : H1 (N * q) Hs' 𝒪) := hy
    rw [← hy', smul_smul, (cd₁.split.idem cd₁.idx).eq]
  have h0 := key v hmem
  rw [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at h0
  exact h0

include hstab mjq mj1 hUact hTp R1 R2 hquad hUunit hβmem in

theorem jDegL_U_eq_alpha_smul (v' : H1 (N * q) Hs' 𝒪)
    (hva : v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx))
    (hv1 : v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx))
    (jmq jm1 : cd.cornerModule)
    (hjmq : (jmq : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v')
    (hjm1 : (jm1 : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v') :
    jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (heckeT (N * q) Hs' q 𝒪 v') = ((αt • jmq : cd.cornerModule) : H1 N Hs 𝒪) ∧
    jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (heckeT (N * q) Hs' q 𝒪 v') = ((αt • jm1 : cd.cornerModule) : H1 N Hs 𝒪) := by
  set v : ↥(Ua cdₐ hstab) := ⟨v', hva⟩ with hvdef
  have eq : jmq = Jq hq' cd cdₐ hstab mjq v := Subtype.ext hjmq
  have e1 : jm1 = J1 h1 cd cdₐ hstab mj1 v := Subtype.ext hjm1
  obtain ⟨hA, hB⟩ := J_U h1 hq' cd cdₐ hstab mjq mj1 U hUact tp hTp R1 R2 v
  have hJ := J1_eq h1 hq' cd cdₐ cd₁ hstab mjq mj1 U hUact tp αt hquad hTp R1 R2 hUunit hβmem v hv1
  have hc := coe_U_smul cdₐ hstab U hUact v
  constructor
  · have : Jq hq' cd cdₐ hstab mjq (U • v) = αt • Jq hq' cd cdₐ hstab mjq v := by
      rw [hB, hJ]
      module
    have := congrArg (fun z : cd.cornerModule => (z : H1 N Hs 𝒪)) this
    simp only [coe_Jq, hc] at this
    rw [this, eq]
  · have : J1 h1 cd cdₐ hstab mj1 (U • v) = αt • J1 h1 cd cdₐ hstab mj1 v := by
      rw [hA, hJ, show algebraMap 𝒪 cd.cornerRing (q : 𝒪) = αt * (tp - αt) from by linear_combination hquad]
      module
    have := congrArg (fun z : cd.cornerModule => (z : H1 N Hs 𝒪)) this
    simp only [coe_J1, hc] at this
    rw [this, e1]

end Main

end CohL2.DCore
p2m_reactivate "P2MW.S_IharaTower_jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement.CohL2 P2MW.S_IharaTower_jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement.CohL2.DCore"
p2m_reactivate "P2MW.S_IharaTower_jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement.CohL2"

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
    (v' : H1 (N * q) Hs' 𝒪)
    (hva : v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx))
    (hv1 : v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx))
    (jmq jm1 : cd.cornerModule)
    (hjmq : (jmq : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v')
    (hjm1 : (jm1 : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v') :
    jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (heckeT (N * q) Hs' q 𝒪 v') = ((αt • jmq : cd.cornerModule) : H1 N Hs 𝒪) ∧
    jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (heckeT (N * q) Hs' q 𝒪 v') = ((αt • jm1 : cd.cornerModule) : H1 N Hs 𝒪) :=
  CohL2.DCore.jDegL_U_eq_alpha_smul h1 hq' cd cdₐ cd₁ hstab mjq mj1 U hUact tp αt hquad hTp R1 R2 hUunit hβmem v' hva hv1 jmq jm1 hjmq hjm1

end S_IharaTower_jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement
end P2MW
export P2MW.S_IharaTower_jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement (solution)
