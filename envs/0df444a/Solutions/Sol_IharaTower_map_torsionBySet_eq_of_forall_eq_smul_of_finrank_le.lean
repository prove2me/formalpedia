-- Prove2me | solution 1 for IharaTower.map_torsionBySet_eq_of_forall_eq_smul_of_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/16a61d98-78c6-5eeb-9a5d-42430938eac2

import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_map_torsionBySet_eq_of_forall_eq_smul_of_finrank_le

set_option autoImplicit false

namespace K1CutIhara

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

theorem eq_zero_of_forall_pow_dvd {ϖ : 𝒪} (hϖ : Irreducible ϖ) {c : 𝒪}
    (h : ∀ n : ℕ, ϖ ^ n ∣ c) : c = 0 := by
  by_contra hc
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have hle : IsDiscreteValuationRing.addVal 𝒪 (ϖ ^ (m + 1)) ≤
      IsDiscreteValuationRing.addVal 𝒪 ((u : 𝒪) * ϖ ^ m) :=
    IsDiscreteValuationRing.addVal_le_iff_dvd.mpr (h (m + 1))
  rw [hϖ.addVal_pow, IsDiscreteValuationRing.addVal_def' u hϖ m] at hle
  have : (m + 1 : ℕ) ≤ m := by exact_mod_cast hle
  omega

theorem eq_zero_of_forall_exists_pow_smul {M : Type} [AddCommGroup M] [Module 𝒪 M]
    [Module.Free 𝒪 M] {ϖ : 𝒪} (hϖ : Irreducible ϖ) (v : M)
    (h : ∀ n : ℕ, ∃ w : M, v = ϖ ^ n • w) : v = 0 := by
  classical
  set b := Module.Free.chooseBasis 𝒪 M with hb
  refine b.ext_elem fun j => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine eq_zero_of_forall_pow_dvd hϖ fun n => ?_
  obtain ⟨w, hw⟩ := h n
  refine ⟨b.repr w j, ?_⟩
  rw [hw, map_smul, Finsupp.smul_apply, smul_eq_mul]

section Modules

variable {M : Type} [AddCommGroup M] [Module 𝒪 M] [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
variable {M' : Type} [AddCommGroup M'] [Module 𝒪 M'] [Module.Finite 𝒪 M'] [Module.Free 𝒪 M']

omit [Module.Finite 𝒪 M] [Module.Finite 𝒪 M'] in

theorem injective_of_residual (i : M →ₗ[𝒪] M') {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : M) (x : M'), i v = ϖ • x → ∃ v₁ : M, v = ϖ • v₁) :
    Function.Injective i := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  refine eq_zero_of_forall_exists_pow_smul hϖ v fun n => ?_
  induction n with
  | zero => exact ⟨v, by rw [pow_zero, one_smul]⟩
  | succ n ih =>
    obtain ⟨w, rfl⟩ := ih

    have hiw : i w = 0 := by
      have h1 : ϖ ^ n • i w = 0 := by rw [← map_smul, hv]
      exact (smul_eq_zero.mp h1).resolve_left (pow_ne_zero n hϖ.ne_zero)
    obtain ⟨w₁, rfl⟩ := hres w 0 (by rw [hiw, smul_zero])
    exact ⟨w₁, by rw [pow_succ, mul_smul]⟩

def IsSaturated (A : Submodule 𝒪 M) : Prop := ∀ (a : 𝒪), a ≠ 0 → ∀ m : M, a • m ∈ A → m ∈ A

omit [Module.Finite 𝒪 M] [Module.Free 𝒪 M] in

theorem isSaturated_of_uniformizer (A : Submodule 𝒪 M) {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (h : ∀ m : M, ϖ • m ∈ A → m ∈ A) : IsSaturated A := by
  intro a ha m ham
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hn : ϖ ^ n • m ∈ A := by
    have := A.smul_mem (↑u⁻¹ : 𝒪) ham
    rwa [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
  clear ham ha
  induction n generalizing m with
  | zero => simpa using hn
  | succ n ih =>
    apply ih
    apply h
    rwa [smul_smul, ← pow_succ']

omit [Module.Finite 𝒪 M] [Module.Free 𝒪 M] [Module.Finite 𝒪 M'] in

theorem isSaturated_map (i : M →ₗ[𝒪] M') {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : M) (x : M'), i v = ϖ • x → ∃ v₁ : M, v = ϖ • v₁)
    (A : Submodule 𝒪 M) (hA : IsSaturated A) : IsSaturated (A.map i) := by
  refine isSaturated_of_uniformizer (A.map i) hϖ fun y hy => ?_
  obtain ⟨x, hxA, hxy⟩ := Submodule.mem_map.mp hy
  obtain ⟨x₁, rfl⟩ := hres x y hxy
  have hx₁ : x₁ ∈ A := hA ϖ hϖ.ne_zero x₁ hxA
  refine Submodule.mem_map.mpr ⟨x₁, hx₁, ?_⟩
  have h2 : ϖ • i x₁ = ϖ • y := by rw [← map_smul, hxy]
  exact smul_right_injective M' hϖ.ne_zero h2

omit [Module.Free 𝒪 M'] in

theorem eq_of_le_of_finrank_le_of_isSaturated (W B : Submodule 𝒪 M') (hWB : W ≤ B)
    (hrk : Module.finrank 𝒪 B ≤ Module.finrank 𝒪 W) (hW : IsSaturated W) : W = B := by
  classical
  haveI : IsNoetherianRing 𝒪 := inferInstance
  haveI : IsNoetherian 𝒪 M' := isNoetherian_of_isNoetherianRing_of_finite 𝒪 M'
  refine le_antisymm hWB fun y hy => ?_

  set W' : Submodule 𝒪 B := W.comap B.subtype with hW'
  have hmap : W'.map B.subtype = W := by
    rw [hW', Submodule.map_comap_subtype, inf_eq_right.mpr hWB]
  have hfinW' : Module.finrank 𝒪 W' = Module.finrank 𝒪 W := by
    rw [← Submodule.finrank_map_subtype_eq B W', hmap]
  have hq : Module.finrank 𝒪 (B ⧸ W') = 0 := by
    have h := Submodule.finrank_quotient_add_finrank W'
    omega
  have htor : Module.IsTorsion 𝒪 (B ⧸ W') := (Module.finrank_eq_zero_iff_isTorsion).mp hq
  obtain ⟨⟨a, ha⟩, hay⟩ := @htor (Submodule.Quotient.mk ⟨y, hy⟩)
  have ha0 : (a : 𝒪) ≠ 0 := nonZeroDivisors.ne_zero ha
  have hmem : a • (⟨y, hy⟩ : B) ∈ W' := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact hay
  have hmem' : a • y ∈ W := by
    have := Submodule.mem_comap.mp hmem
    simpa using this
  exact hW a ha0 y hmem'

end Modules

end K1CutIhara

open K1CutIhara in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] {T' : Type} [CommRing T'] [Algebra 𝒪 T']
    {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    [Module.Finite 𝒪 M'] [Module.Free 𝒪 M']
    (i : M →ₗ[𝒪] M') (πT : T →ₐ[𝒪] 𝒪) (πT' : T' →ₐ[𝒪] 𝒪)
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : M) (x : M'), i v = ϖ • x → ∃ v₁ : M, v = ϖ • v₁)
    (hincl : Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) ≤
      (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪)
    (hrank : Module.finrank 𝒪
        ((Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪) ≤
      Module.finrank 𝒪 ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪)) :
    Function.Injective i ∧
    Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) =
      (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪 := by
  classical
  have hinj : Function.Injective i := injective_of_residual i hϖ hres
  refine ⟨hinj, ?_⟩
  set A : Submodule 𝒪 M := (Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪
    with hAdef
  set B : Submodule 𝒪 M' :=
    (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪 with hBdef

  have hAsat : IsSaturated A := by
    intro a ha m ham
    rw [hAdef, Submodule.restrictScalars_mem, Submodule.mem_torsionBySet_iff] at ham ⊢
    intro t
    have h1 : a • ((t : T) • m) = 0 := by rw [smul_comm, ham t]
    exact (smul_eq_zero.mp h1).resolve_left ha

  have hWsat : IsSaturated (A.map i) := isSaturated_map i hϖ hres A hAsat

  have hrk : Module.finrank 𝒪 B ≤ Module.finrank 𝒪 (A.map i) := by
    rw [(Submodule.equivMapOfInjective i hinj A).symm.finrank_eq]
    exact hrank
  exact eq_of_le_of_finrank_le_of_isSaturated (A.map i) B hincl hrk hWsat

end S_IharaTower_map_torsionBySet_eq_of_forall_eq_smul_of_finrank_le
end P2MW
export P2MW.S_IharaTower_map_torsionBySet_eq_of_forall_eq_smul_of_finrank_le (solution)
