-- Prove2me | solution 1 for ModularCurve.MazurII142.OdaDictionaryNoBT1.finrank_eq_two_of_finrank_ker_frob_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8423ef00-6294-5ac4-93cf-5a5dfc7418d5

import Mathlib
import Definitions.Def_HeckeGalois_MazurCase1BundleNoBT1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq

universe u v w

noncomputable section

p2m_open "Module P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.Module"

section AbstractDieudonneUpper

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]

namespace Module p2m_export "Module" "Injective finrank mk finrank_pos_iff_of_free End Finite.of_surjective" end Module
p2m_open_scoped "Module" in

private theorem Module.finrank_range_add_finrank_quotient_range [FiniteDimensional k M]
    (V : Module.End k M) :
    finrank k (LinearMap.range V) + finrank k (M ⧸ LinearMap.range V) = finrank k M := by
  rw [add_comm]; exact Submodule.finrank_quotient_add_finrank _

namespace Module p2m_export "Module" "Injective finrank mk finrank_pos_iff_of_free End Finite.of_surjective" namespace End end Module.End
p2m_open_scoped "Module Module.End" in

private theorem Module.End.range_le_ker_of_comp_eq_zero {F V : Module.End k M} (hFV : F ∘ₗ V = 0) :
    LinearMap.range V ≤ LinearMap.ker F :=
  LinearMap.range_le_ker_iff.mpr hFV

p2m_open_scoped "Module" in

private theorem Module.finrank_le_two_of_comp_eq_zero_of_ker_eq_coker_le_one [FiniteDimensional k M]
    {F V : Module.End k M} (hFV : F ∘ₗ V = 0)
    (hdual : finrank k (LinearMap.ker F) = finrank k (M ⧸ LinearMap.range V))
    (hcoker : finrank k (M ⧸ LinearMap.range V) ≤ 1) :
    finrank k M ≤ 2 := by
  have hrange_le : finrank k (LinearMap.range V) ≤ finrank k (LinearMap.ker F) :=
    Submodule.finrank_mono (Module.End.range_le_ker_of_comp_eq_zero hFV)
  calc finrank k M
      = finrank k (LinearMap.range V) + finrank k (M ⧸ LinearMap.range V) :=
        (Module.finrank_range_add_finrank_quotient_range V).symm
    _ ≤ finrank k (LinearMap.ker F) + finrank k (M ⧸ LinearMap.range V) :=
        Nat.add_le_add_right hrange_le _
    _ = finrank k (M ⧸ LinearMap.range V) + finrank k (M ⧸ LinearMap.range V) := by rw [hdual]
    _ ≤ 1 + 1 := Nat.add_le_add hcoker hcoker
    _ = 2 := rfl

end AbstractDieudonneUpper

namespace ModularCurve
p2m_export "ModularCurve" "MazurII142.OdaDictionaryNoBT1"
p2m_open "ModularCurve"

section Forms

variable (𝕋 : Type*) [CommRing 𝕋] (J : Type*) [AddCommGroup J] [Module 𝕋 J] (𝔪 : Ideal 𝕋)

private def MultiplicityOne : Prop :=
  Module.finrank (𝕋 ⧸ 𝔪) (Submodule.torsionBySet 𝕋 J 𝔪) = 2

end Forms

namespace MazurII142
p2m_export "ModularCurve.MazurII142" "OdaDictionaryNoBT1 VerFrobPair VerFrobPair.SelfDual"
p2m_open "ModularCurve.MazurII142"

namespace VerFrobPair
p2m_export "ModularCurve.MazurII142.VerFrobPair" "ver_frob_apply frob_ver_apply SelfDual Stable quotientPair kernelPair ver frob_comp_ver mk frob"
p2m_open "ModularCurve.MazurII142.VerFrobPair"

section Basic

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
variable (D : VerFrobPair k M)

private theorem _root_.ModularCurve.MazurII142.VerFrobPair.frob_eq_zero_of_ver_surjective (h : Function.Surjective D.ver) : D.frob = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := h x
  simpa using D.frob_ver_apply y

p2m_export "ModularCurve.MazurII142.VerFrobPair" "frob_eq_zero_of_ver_surjective"

private theorem _root_.ModularCurve.MazurII142.VerFrobPair.ver_eq_zero_of_frob_surjective (h : Function.Surjective D.frob) : D.ver = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := h x
  simpa using D.ver_frob_apply y

p2m_export "ModularCurve.MazurII142.VerFrobPair" "ver_eq_zero_of_frob_surjective"

private theorem _root_.ModularCurve.MazurII142.VerFrobPair.not_surjective_ver_of_frob_ne_zero (h : D.frob ≠ 0) :
    ¬ Function.Surjective D.ver :=
  fun hs => h (D.frob_eq_zero_of_ver_surjective hs)

p2m_export "ModularCurve.MazurII142.VerFrobPair" "not_surjective_ver_of_frob_ne_zero"

private theorem _root_.ModularCurve.MazurII142.VerFrobPair.not_surjective_frob_of_ver_ne_zero (h : D.ver ≠ 0) :
    ¬ Function.Surjective D.frob :=
  fun hs => h (D.ver_eq_zero_of_frob_surjective hs)

p2m_export "ModularCurve.MazurII142.VerFrobPair" "not_surjective_frob_of_ver_ne_zero"
private theorem _root_.ModularCurve.MazurII142.VerFrobPair.not_bijective_ver_of_frob_ne_zero (h : D.frob ≠ 0) :
    ¬ Function.Bijective D.ver :=
  fun hb => D.not_surjective_ver_of_frob_ne_zero h hb.2

p2m_export "ModularCurve.MazurII142.VerFrobPair" "not_bijective_ver_of_frob_ne_zero"
private theorem _root_.ModularCurve.MazurII142.VerFrobPair.not_bijective_frob_of_ver_ne_zero (h : D.ver ≠ 0) :
    ¬ Function.Bijective D.frob :=
  fun hb => D.not_surjective_frob_of_ver_ne_zero h hb.2

p2m_export "ModularCurve.MazurII142.VerFrobPair" "not_bijective_frob_of_ver_ne_zero"
end Basic

section Duality

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]

namespace SelfDual
p2m_export "ModularCurve.MazurII142.VerFrobPair.SelfDual" "mk"
p2m_open "ModularCurve.MazurII142.VerFrobPair.SelfDual"

variable {D : VerFrobPair k M}

private theorem ver_eq_zero_of_frob_eq_zero [FiniteDimensional k M]
    (hrank : finrank k (LinearMap.ker D.frob) = finrank k (M ⧸ LinearMap.range D.ver))
    (h : D.frob = 0) : D.ver = 0 := by
  have h1 : finrank k (LinearMap.ker D.frob) = finrank k M := by
    rw [h, LinearMap.ker_zero, finrank_top]
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range D.ver)
  have h3 : finrank k (LinearMap.range D.ver) = 0 := by omega
  exact LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h3)

private theorem mazurII144 [FiniteDimensional k M]
    (hrank : finrank k (LinearMap.ker D.frob) = finrank k (M ⧸ LinearMap.range D.ver))
    (hdim : 2 ≤ finrank k M)
    (hcoker : finrank k (M ⧸ LinearMap.range D.ver) ≤ 1) :
    D.frob ≠ 0 ∧ D.ver ≠ 0 ∧
      ¬ Function.Bijective D.frob ∧ ¬ Function.Bijective D.ver := by
  have hver : D.ver ≠ 0 := by
    intro h
    rw [h, LinearMap.range_zero] at hcoker
    have hbot := Submodule.finrank_quotient_add_finrank (⊥ : Submodule k M)
    simp only [finrank_bot, add_zero] at hbot
    omega
  have hfrob : D.frob ≠ 0 := fun h => hver (ver_eq_zero_of_frob_eq_zero hrank h)
  exact ⟨hfrob, hver, D.not_bijective_frob_of_ver_ne_zero hver,
    D.not_bijective_ver_of_frob_ne_zero hfrob⟩

private theorem finrank_le_two [FiniteDimensional k M]
    (hrank : finrank k (LinearMap.ker D.frob) = finrank k (M ⧸ LinearMap.range D.ver))
    (hcoker : finrank k (M ⧸ LinearMap.range D.ver) ≤ 1) :
    finrank k M ≤ 2 :=
  Module.finrank_le_two_of_comp_eq_zero_of_ker_eq_coker_le_one
    (F := D.frob) (V := D.ver) D.frob_comp_ver
    hrank hcoker

end SelfDual

end Duality

section QuotientEngine

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
variable (D : VerFrobPair k M)

@[scoped simp]
private theorem quotientPair_ver_apply_mk (N : Submodule k M) (hN : D.Stable N) (x : M) :
    (D.quotientPair N hN).ver (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (D.ver x) :=
  rfl

private theorem _root_.ModularCurve.MazurII142.VerFrobPair.ver_quotientPair_bijective_of_bijective [FiniteDimensional k M]
    (N : Submodule k M) (hN : D.Stable N) (hbij : Function.Bijective D.ver) :
    Function.Bijective (D.quotientPair N hN).ver := by
  have hsurj : Function.Surjective (D.quotientPair N hN).ver := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N z
    obtain ⟨y, hy⟩ := hbij.2 x
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rw [quotientPair_ver_apply_mk, hy]
  exact ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩

p2m_export "ModularCurve.MazurII142.VerFrobPair" "ver_quotientPair_bijective_of_bijective"
end QuotientEngine

end VerFrobPair
p2m_reactivate "P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve.MazurII142.VerFrobPair"

section SnakeEngine

variable {k : Type*} [Field k] {M₁ M₂ M₃ : Type*}
  [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
  [AddCommGroup M₃] [Module k M₃]

private theorem finrank_le_of_surjective {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V]
    (f : V →ₗ[k] W) (hf : Function.Surjective f) : finrank k W ≤ finrank k V := by
  have h1 : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf
  have h2 : finrank k (LinearMap.range f) = finrank k W := by
    rw [h1, finrank_top]
  rw [← h2]
  exact LinearMap.finrank_range_le f

private def cokerVerMap (D₂ : VerFrobPair k M₂) (D₃ : VerFrobPair k M₃) (π : M₂ →ₗ[k] M₃)
    (hπ_ver : π ∘ₗ D₂.ver = D₃.ver ∘ₗ π) :
    (M₂ ⧸ LinearMap.range D₂.ver) →ₗ[k] (M₃ ⧸ LinearMap.range D₃.ver) :=
  Submodule.mapQ _ _ π (by
    rintro x ⟨y, rfl⟩
    simp only [Submodule.mem_comap, LinearMap.mem_range]
    exact ⟨π y, by simpa using (LinearMap.congr_fun hπ_ver y).symm⟩)

@[scoped simp]
private theorem cokerVerMap_apply_mk (D₂ : VerFrobPair k M₂) (D₃ : VerFrobPair k M₃)
    (π : M₂ →ₗ[k] M₃) (hπ_ver : π ∘ₗ D₂.ver = D₃.ver ∘ₗ π) (x : M₂) :
    cokerVerMap D₂ D₃ π hπ_ver (Submodule.Quotient.mk x) = Submodule.Quotient.mk (π x) :=
  rfl

private theorem cokerVerMap_surjective (D₂ : VerFrobPair k M₂) (D₃ : VerFrobPair k M₃)
    (π : M₂ →ₗ[k] M₃) (hπ_ver : π ∘ₗ D₂.ver = D₃.ver ∘ₗ π)
    (hπ : Function.Surjective π) :
    Function.Surjective (cokerVerMap D₂ D₃ π hπ_ver) := by
  intro z
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨y, rfl⟩ := hπ w
  exact ⟨Submodule.Quotient.mk y, rfl⟩

private theorem mazurII145 (D₂ : VerFrobPair k M₂) (D₃ : VerFrobPair k M₃) (π : M₂ →ₗ[k] M₃)
    [FiniteDimensional k M₂] [FiniteDimensional k M₃]
    (hπ_ver : π ∘ₗ D₂.ver = D₃.ver ∘ₗ π) (hπ : Function.Surjective π)
    (ha : finrank k (M₂ ⧸ LinearMap.range D₂.ver) ≤ 1)
    (hb : D₃.frob ≠ 0) :
    Function.Bijective (cokerVerMap D₂ D₃ π hπ_ver) ∧
      finrank k (M₂ ⧸ LinearMap.range D₂.ver) = 1 ∧
      finrank k (M₃ ⧸ LinearMap.range D₃.ver) = 1 := by
  have hns : ¬ Function.Surjective D₃.ver := D₃.not_surjective_ver_of_frob_ne_zero hb
  have hne_top : LinearMap.range D₃.ver ≠ ⊤ := fun h => hns (LinearMap.range_eq_top.mp h)
  haveI : Nontrivial (M₃ ⧸ LinearMap.range D₃.ver) :=
    Submodule.Quotient.nontrivial_iff.mpr hne_top
  have h3pos : 0 < finrank k (M₃ ⧸ LinearMap.range D₃.ver) :=
    (Module.finrank_pos_iff_of_free k _).mpr inferInstance
  have hsurj := cokerVerMap_surjective D₂ D₃ π hπ_ver hπ
  have hle : finrank k (M₃ ⧸ LinearMap.range D₃.ver)
      ≤ finrank k (M₂ ⧸ LinearMap.range D₂.ver) :=
    finrank_le_of_surjective _ hsurj
  have h2eq : finrank k (M₂ ⧸ LinearMap.range D₂.ver) = 1 := by omega
  have h3eq : finrank k (M₃ ⧸ LinearMap.range D₃.ver) = 1 := by omega
  refine ⟨⟨?_, hsurj⟩, h2eq, h3eq⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [h2eq, h3eq])).mpr hsurj

private theorem mazurII146_snake (D₁ : VerFrobPair k M₁) (D₂ : VerFrobPair k M₂)
    (D₃ : VerFrobPair k M₃) (ι : M₁ →ₗ[k] M₂) (π : M₂ →ₗ[k] M₃)
    [FiniteDimensional k M₂]
    (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hexact : LinearMap.range ι = LinearMap.ker π)
    (hι_ver : ι ∘ₗ D₁.ver = D₂.ver ∘ₗ ι)
    (hπ_ver : π ∘ₗ D₂.ver = D₃.ver ∘ₗ π)
    (hπ_frob : π ∘ₗ D₂.frob = D₃.frob ∘ₗ π)
    (ha : finrank k (M₂ ⧸ LinearMap.range D₂.ver) ≤ 1)
    (hb : D₃.frob ≠ 0) :
    Function.Bijective D₁.ver := by
  haveI : FiniteDimensional k M₁ := FiniteDimensional.of_injective ι hι
  haveI : FiniteDimensional k M₃ := Module.Finite.of_surjective π hπ
  have hπ_ver' : ∀ y : M₂, π (D₂.ver y) = D₃.ver (π y) := fun y => by
    simpa using LinearMap.congr_fun hπ_ver y
  have hπ_frob' : ∀ y : M₂, π (D₂.frob y) = D₃.frob (π y) := fun y => by
    simpa using LinearMap.congr_fun hπ_frob y
  have hι_ver' : ∀ x : M₁, ι (D₁.ver x) = D₂.ver (ι x) := fun x => by
    simpa using LinearMap.congr_fun hι_ver x
  obtain ⟨⟨hγinj, _⟩, h2eq, h3eq⟩ := mazurII145 D₂ D₃ π hπ_ver hπ ha hb
  have hker2 : finrank k (LinearMap.ker D₂.ver) = 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker D₂.ver
    have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range D₂.ver)
    omega
  have hker3 : finrank k (LinearMap.ker D₃.ver) = 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker D₃.ver
    have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range D₃.ver)
    omega
  have hπ_ker : ∀ x ∈ LinearMap.ker D₂.ver, π x ∈ LinearMap.ker D₃.ver := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← hπ_ver' x, hx, map_zero]
  set β : (LinearMap.ker D₂.ver) →ₗ[k] (LinearMap.ker D₃.ver) :=
    π.restrict hπ_ker with hβ_def
  obtain ⟨x₃, hx₃⟩ : ∃ x₃ : M₃, D₃.frob x₃ ≠ 0 := by
    by_contra hcon
    refine hb (LinearMap.ext fun x => ?_)
    rw [LinearMap.zero_apply]
    by_contra hx
    exact hcon ⟨x, hx⟩
  obtain ⟨y₀, hy₀⟩ := hπ x₃
  have hy₀_ker : D₂.frob y₀ ∈ LinearMap.ker D₂.ver := by
    rw [LinearMap.mem_ker]
    exact D₂.ver_frob_apply y₀
  have hβ_ne : β ⟨D₂.frob y₀, hy₀_ker⟩ ≠ 0 := by
    intro h0
    apply hx₃
    have hval : π (D₂.frob y₀) = 0 := by
      have hcoe := congrArg Subtype.val h0
      rwa [hβ_def, LinearMap.coe_restrict_apply] at hcoe
    rw [← hy₀, ← hπ_frob' y₀]
    exact hval
  have hβ_surj : Function.Surjective β := by
    rw [← LinearMap.range_eq_top]
    have hr_ne_bot : LinearMap.range β ≠ ⊥ := by
      intro hbot
      apply hβ_ne
      have hmem : β ⟨D₂.frob y₀, hy₀_ker⟩ ∈ LinearMap.range β :=
        LinearMap.mem_range_self β _
      rwa [hbot, Submodule.mem_bot] at hmem
    have hr_pos : 0 < finrank k (LinearMap.range β) := by
      haveI : Nontrivial (LinearMap.range β) :=
        Submodule.nontrivial_iff_ne_bot.mpr hr_ne_bot
      exact (Module.finrank_pos_iff_of_free k _).mpr inferInstance
    have hr_le : finrank k (LinearMap.range β) ≤ finrank k (LinearMap.ker D₃.ver) :=
      Submodule.finrank_le _
    rw [Submodule.eq_top_iff_finrank_eq]
    omega
  have hver1_surj : Function.Surjective D₁.ver := by
    intro x
    have hπιx : π (ι x) = 0 := by
      have hmem : ι x ∈ LinearMap.ker π := by
        rw [← hexact]
        exact LinearMap.mem_range_self ι x
      rwa [LinearMap.mem_ker] at hmem
    have hA : ι x ∈ LinearMap.range D₂.ver := by
      have hγ0 : (cokerVerMap D₂ D₃ π hπ_ver) (Submodule.Quotient.mk (ι x)) = 0 := by
        rw [cokerVerMap_apply_mk, hπιx, Submodule.Quotient.mk_zero]
      have hmk : (Submodule.Quotient.mk (ι x) :
          M₂ ⧸ LinearMap.range D₂.ver) = 0 := by
        apply hγinj
        rw [hγ0, map_zero]
      rwa [Submodule.Quotient.mk_eq_zero] at hmk
    obtain ⟨y, hy⟩ := hA
    have hπy_ker : π y ∈ LinearMap.ker D₃.ver := by
      rw [LinearMap.mem_ker, ← hπ_ver' y, hy, hπιx]
    obtain ⟨⟨z, hz_ker⟩, hz⟩ := hβ_surj ⟨π y, hπy_ker⟩
    have hπz : π z = π y := by
      have hcoe := congrArg Subtype.val hz
      rwa [hβ_def, LinearMap.coe_restrict_apply] at hcoe
    have hyz : y - z ∈ LinearMap.range ι := by
      rw [hexact, LinearMap.mem_ker, map_sub, hπz, sub_self]
    obtain ⟨w, hw⟩ := hyz
    refine ⟨w, hι ?_⟩
    rw [hι_ver' w, hw, map_sub]
    have hz0 : D₂.ver z = 0 := by rwa [LinearMap.mem_ker] at hz_ker
    rw [hz0, sub_zero, hy]
  exact ⟨LinearMap.injective_iff_surjective.mpr hver1_surj, hver1_surj⟩

end SnakeEngine
p2m_reactivate "P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve.MazurII142.VerFrobPair"

section Collapse

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
  {W : Type*} [AddCommGroup W] [Module k W]

private theorem ver_bijective_of_equivariant_equiv (D : VerFrobPair k M) (DW : VerFrobPair k W)
    (e : M ≃ₗ[k] W) (he_ver : ∀ x : M, e (D.ver x) = DW.ver (e x))
    (hbij : Function.Bijective D.ver) : Function.Bijective DW.ver := by
  have key : ∀ w : W, DW.ver w = e (D.ver (e.symm w)) := by
    intro w
    rw [he_ver (e.symm w), e.apply_symm_apply]
  constructor
  · intro a b hab
    rw [key a, key b] at hab
    have h1 := hbij.1 (e.injective hab)
    have h2 := congrArg e h1
    rwa [e.apply_symm_apply, e.apply_symm_apply] at h2
  · intro w
    obtain ⟨x, hx⟩ := hbij.2 (e.symm w)
    refine ⟨e x, ?_⟩
    rw [key (e x), e.symm_apply_apply, hx, e.apply_symm_apply]

private theorem collapse_subsingleton_of_layer [FiniteDimensional k M]
    (D : VerFrobPair k M) (DW : VerFrobPair k W)
    (hbij : Function.Bijective D.ver)
    (hWnbij : ¬ Function.Bijective DW.ver)
    (hlayer : Nontrivial M → ∃ (N : Submodule k M) (hN : D.Stable N)
      (e : (M ⧸ N) ≃ₗ[k] W),
        ∀ z : M ⧸ N, e ((D.quotientPair N hN).ver z) = DW.ver (e z)) :
    Subsingleton M := by
  by_contra hcon
  rw [not_subsingleton_iff_nontrivial] at hcon
  obtain ⟨N, hN, e, he⟩ := hlayer hcon
  exact hWnbij (ver_bijective_of_equivariant_equiv (D.quotientPair N hN) DW e he
    (D.ver_quotientPair_bijective_of_bijective N hN hbij))

end Collapse
p2m_reactivate "P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve.MazurII142.VerFrobPair"

section Case1

variable {k : Type*} [Field k] {M₂ M₃ : Type*}
  [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃] [Module k M₃]

private theorem mazurII142_case1_dieudonne [FiniteDimensional k M₂]
    (D₂ : VerFrobPair k M₂) (D₃ : VerFrobPair k M₃)
    (π : M₂ →ₗ[k] M₃) (hπ : Function.Surjective π)
    (hπ_ver : π ∘ₗ D₂.ver = D₃.ver ∘ₗ π) (hπ_frob : π ∘ₗ D₂.frob = D₃.frob ∘ₗ π)
    (ha : finrank k (M₂ ⧸ LinearMap.range D₂.ver) ≤ 1)
    (hrank : finrank k (LinearMap.ker D₃.frob) = finrank k (M₃ ⧸ LinearMap.range D₃.ver))
    (hdim : 2 ≤ finrank k M₃)
    (hlayer : Nontrivial (LinearMap.ker π) →
      ∃ (N : Submodule k (LinearMap.ker π))
        (hN : (D₂.kernelPair D₃ π hπ_ver hπ_frob).Stable N)
        (e : ((LinearMap.ker π) ⧸ N) ≃ₗ[k] M₃),
        ∀ z, e (((D₂.kernelPair D₃ π hπ_ver hπ_frob).quotientPair N hN).ver z)
          = D₃.ver (e z)) :
    Function.Bijective π ∧ finrank k M₂ = finrank k M₃ := by
  haveI : FiniteDimensional k M₃ := Module.Finite.of_surjective π hπ
  have hcoker3 : finrank k (M₃ ⧸ LinearMap.range D₃.ver) ≤ 1 := by
    have hsurj := cokerVerMap_surjective D₂ D₃ π hπ_ver hπ
    exact le_trans (finrank_le_of_surjective _ hsurj) ha
  obtain ⟨hfrob3_ne, _, _, hver3_nbij⟩ := VerFrobPair.SelfDual.mazurII144 hrank hdim hcoker3
  have hker_bij : Function.Bijective (D₂.kernelPair D₃ π hπ_ver hπ_frob).ver := by
    refine mazurII146_snake (D₂.kernelPair D₃ π hπ_ver hπ_frob) D₂ D₃
      (LinearMap.ker π).subtype π (Submodule.injective_subtype _) hπ
      (Submodule.range_subtype _) ?_ hπ_ver hπ_frob ha hfrob3_ne
    apply LinearMap.ext
    intro x
    rfl
  haveI hker_sub : Subsingleton (LinearMap.ker π) :=
    collapse_subsingleton_of_layer (D₂.kernelPair D₃ π hπ_ver hπ_frob) D₃
      hker_bij hver3_nbij hlayer
  have hker_bot : LinearMap.ker π = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have helim := Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker π) ⟨0, Submodule.zero_mem _⟩
    exact congrArg Subtype.val helim
  have hπ_inj : Function.Injective π := LinearMap.ker_eq_bot.mp hker_bot
  exact ⟨⟨hπ_inj, hπ⟩, (LinearEquiv.ofBijective π ⟨hπ_inj, hπ⟩).finrank_eq⟩

end Case1
p2m_reactivate "P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve.MazurII142.VerFrobPair"

section Bridge

private theorem multiplicityOne_of_finrank_chain
    {𝕋 : Type*} [CommRing 𝕋] {J : Type*} [AddCommGroup J] [Module 𝕋 J] {𝔪 : Ideal 𝕋}
    {k : Type*} [Field k] {M₂ M₃ : Type*}
    [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃] [Module k M₃]
    (hoda : Module.finrank (𝕋 ⧸ 𝔪) (Submodule.torsionBySet 𝕋 J 𝔪) = finrank k M₂)
    (hcase1 : finrank k M₂ = finrank k M₃)
    (hdim3 : finrank k M₃ = 2) :
    ModularCurve.MultiplicityOne 𝕋 J 𝔪 :=
  hoda.trans (hcase1.trans hdim3)

private theorem multiplicityOne_of_dieudonne_case1
    {𝕋 : Type*} [CommRing 𝕋] {J : Type*} [AddCommGroup J] [Module 𝕋 J] {𝔪 : Ideal 𝕋}
    {k : Type*} [Field k] {M₂ M₃ : Type*}
    [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃] [Module k M₃]
    [FiniteDimensional k M₂]
    (D₂ : VerFrobPair k M₂) (D₃ : VerFrobPair k M₃)
    (π : M₂ →ₗ[k] M₃) (hπ : Function.Surjective π)
    (hπ_ver : π ∘ₗ D₂.ver = D₃.ver ∘ₗ π) (hπ_frob : π ∘ₗ D₂.frob = D₃.frob ∘ₗ π)
    (ha : finrank k (M₂ ⧸ LinearMap.range D₂.ver) ≤ 1)
    (hrank : finrank k (LinearMap.ker D₃.frob) = finrank k (M₃ ⧸ LinearMap.range D₃.ver))
    (hlayer : Nontrivial (LinearMap.ker π) →
      ∃ (N : Submodule k (LinearMap.ker π))
        (hN : (D₂.kernelPair D₃ π hπ_ver hπ_frob).Stable N)
        (e : ((LinearMap.ker π) ⧸ N) ≃ₗ[k] M₃),
        ∀ z, e (((D₂.kernelPair D₃ π hπ_ver hπ_frob).quotientPair N hN).ver z)
          = D₃.ver (e z))
    (hoda : Module.finrank (𝕋 ⧸ 𝔪) (Submodule.torsionBySet 𝕋 J 𝔪) = finrank k M₂)
    (hdim3 : finrank k M₃ = 2) :
    ModularCurve.MultiplicityOne 𝕋 J 𝔪 := by
  obtain ⟨_, hrank⟩ := mazurII142_case1_dieudonne D₂ D₃ π hπ hπ_ver hπ_frob ha hrank
    (by rw [hdim3]) hlayer
  exact multiplicityOne_of_finrank_chain hoda hrank hdim3

end Bridge
p2m_reactivate "P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve.MazurII142.VerFrobPair"

namespace OdaDictionaryNoBT1
p2m_export "ModularCurve.MazurII142.OdaDictionaryNoBT1" "kernelPair FontaineLayer DHDR mk rank_V pi_ver pi_surjective hodgeSub hodgeQuot pi rank_J pi_frob DMV"
p2m_open "ModularCurve.MazurII142.OdaDictionaryNoBT1"

section Derived

variable {𝕋 : Type*} [CommRing 𝕋] {J : Type*} [AddCommGroup J] [Module 𝕋 J] {𝔪 : Ideal 𝕋}
  {k : Type*} [Field k]
  {Vrep : Type*} [AddCommGroup Vrep] [Module (𝕋 ⧸ 𝔪) Vrep]
  {HDR : Type*} [AddCommGroup HDR] [Module k HDR]
  {MV : Type*} [AddCommGroup MV] [Module k MV]
  {H0Ω : Type*} [AddCommGroup H0Ω] [Module k H0Ω]
  {H1O : Type*} [AddCommGroup H1O] [Module k H1O]
  (P : OdaDictionaryNoBT1 𝕋 J 𝔪 k Vrep HDR MV H0Ω H1O)

private theorem _root_.ModularCurve.MazurII142.OdaDictionaryNoBT1.coker_ver_le_one (h94 : finrank k H1O ≤ 1) :
    finrank k (HDR ⧸ LinearMap.range P.DHDR.ver) ≤ 1 := by
  rw [← P.hodgeQuot.finrank_eq]
  exact h94

p2m_export "ModularCurve.MazurII142.OdaDictionaryNoBT1" "coker_ver_le_one"

private theorem finrank_ker_frob :
    finrank k (LinearMap.ker P.DHDR.frob) = finrank k H0Ω :=
  P.hodgeSub.finrank_eq.symm

private theorem _root_.ModularCurve.MazurII142.OdaDictionaryNoBT1.mazurII143 [FiniteDimensional k HDR] (h94 : finrank k H1O ≤ 1) :
    finrank k (MV ⧸ LinearMap.range P.DMV.ver) ≤ 1 := by
  have hsurj : Function.Surjective (cokerVerMap P.DHDR P.DMV P.pi P.pi_ver) :=
    cokerVerMap_surjective P.DHDR P.DMV P.pi P.pi_ver P.pi_surjective
  have hle : finrank k (MV ⧸ LinearMap.range P.DMV.ver)
      ≤ finrank k (HDR ⧸ LinearMap.range P.DHDR.ver) :=
    LinearMap.finrank_le_finrank_of_surjective hsurj
  exact le_trans hle (P.coker_ver_le_one h94)

p2m_export "ModularCurve.MazurII142.OdaDictionaryNoBT1" "mazurII143"

private theorem pi_bijective [FiniteDimensional k HDR]
    (h94 : finrank k H1O ≤ 1)
    (hrank : finrank k (LinearMap.ker P.DMV.frob) = finrank k (MV ⧸ LinearMap.range P.DMV.ver))
    (hlayer : P.FontaineLayer)
    (hdimMV : 2 ≤ finrank k MV) :
    Function.Bijective P.pi ∧ finrank k HDR = finrank k MV :=
  mazurII142_case1_dieudonne P.DHDR P.DMV P.pi P.pi_surjective P.pi_ver P.pi_frob
    (P.coker_ver_le_one h94) hrank hdimMV hlayer

private theorem _root_.ModularCurve.MazurII142.OdaDictionaryNoBT1.multiplicityOne [FiniteDimensional k HDR]
    (h94 : finrank k H1O ≤ 1)
    (hrank : finrank k (LinearMap.ker P.DMV.frob) = finrank k (MV ⧸ LinearMap.range P.DMV.ver))
    (hlayer : P.FontaineLayer)
    (hdimV : Module.finrank (𝕋 ⧸ 𝔪) Vrep = 2) :
    ModularCurve.MultiplicityOne 𝕋 J 𝔪 :=
  multiplicityOne_of_dieudonne_case1 P.DHDR P.DMV P.pi P.pi_surjective P.pi_ver P.pi_frob
    (P.coker_ver_le_one h94) hrank hlayer P.rank_J (P.rank_V.symm.trans hdimV)

p2m_export "ModularCurve.MazurII142.OdaDictionaryNoBT1" "multiplicityOne"

private theorem finrank_MV_le_two [FiniteDimensional k HDR]
    (h94 : finrank k H1O ≤ 1)
    (hrank : finrank k (LinearMap.ker P.DMV.frob) = finrank k (MV ⧸ LinearMap.range P.DMV.ver)) :
    finrank k MV ≤ 2 := by
  haveI : FiniteDimensional k MV := Module.Finite.of_surjective P.pi P.pi_surjective
  exact VerFrobPair.SelfDual.finrank_le_two hrank (P.mazurII143 h94)

end Derived
p2m_reactivate "P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve.MazurII142.VerFrobPair"

end OdaDictionaryNoBT1
p2m_reactivate "P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve.MazurII142.VerFrobPair"

end MazurII142
p2m_reactivate "P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve.MazurII142.VerFrobPair P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve.MazurII142"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve.MazurII142.VerFrobPair P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve.MazurII142 P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve"

set_option autoImplicit false
attribute [local instance] Ideal.Quotient.field in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve in

theorem solution
    {𝕋 : Type u} [CommRing 𝕋] {J : Type v} [AddCommGroup J] [Module 𝕋 J] {𝔪 : Ideal 𝕋} [𝔪.IsMaximal]
    {Vrep : Type w} [AddCommGroup Vrep] [Module (𝕋 ⧸ 𝔪) Vrep]
    {HDR : Type w} [AddCommGroup HDR] [Module (𝕋 ⧸ 𝔪) HDR]
    {MV : Type w} [AddCommGroup MV] [Module (𝕋 ⧸ 𝔪) MV]
    {H0Ω : Type w} [AddCommGroup H0Ω] [Module (𝕋 ⧸ 𝔪) H0Ω]
    {H1O : Type w} [AddCommGroup H1O] [Module (𝕋 ⧸ 𝔪) H1O]
    (P : MazurII142.OdaDictionaryNoBT1 𝕋 J 𝔪 (𝕋 ⧸ 𝔪) Vrep HDR MV H0Ω H1O)
    [FiniteDimensional (𝕋 ⧸ 𝔪) HDR]
    (hrank : Module.finrank (𝕋 ⧸ 𝔪) ↥(LinearMap.ker P.DMV.frob) =
      Module.finrank (𝕋 ⧸ 𝔪) (MV ⧸ LinearMap.range P.DMV.ver))
    (hlayer : P.FontaineLayer)
    (h94 : Module.finrank (𝕋 ⧸ 𝔪) H1O ≤ 1)
    (hdimV : Module.finrank (𝕋 ⧸ 𝔪) Vrep = 2) :
    Module.finrank (𝕋 ⧸ 𝔪) ↥(Submodule.torsionBySet 𝕋 J 𝔪) = 2 :=
  P.multiplicityOne h94 hrank hlayer hdimV

end
p2m_reactivate "P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve.MazurII142.VerFrobPair P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve.MazurII142 P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq.ModularCurve"

end S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq
end P2MW
export P2MW.S_ModularCurve_MazurII142_OdaDictionaryNoBT1_finrank_eq_two_of_finrank_ker_frob_eq (solution)
