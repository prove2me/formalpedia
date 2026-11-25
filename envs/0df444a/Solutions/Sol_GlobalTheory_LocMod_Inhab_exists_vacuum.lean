-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.exists_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:00:33.058037+00:00
-- url     : https://prove2.me/submissions/ffa08a36-57bf-4dbd-8d60-fecd66384f9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Theorems.Thm_GlobalTheory_LocMod_Inhab_exists_fixed
import Theorems.Thm_GlobalTheory_LocMod_Inhab_finite_box
import Theorems.Thm_GlobalTheory_LocMod_Inhab_exists_box_subset
import Theorems.Thm_GlobalTheory_LocMod_Inhab_pairing_comm
import Theorems.Thm_GlobalTheory_LocMod_Inhab_isBichar_pairing
import Theorems.Thm_GlobalTheory_LocMod_Inhab_exists_sep
import Theorems.Thm_GlobalTheory_LocMod_Inhab_pairing_box
import Theorems.Thm_GlobalTheory_PlaceModel_IsBichar_neg_mul
import Theorems.Thm_GlobalTheory_SplitWeil_exists_hasConductor_of_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology
open GlobalTheory GlobalTheory.LocMod GlobalTheory.LocMod.Inhab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
namespace GlobalTheory.LocMod.Inhab
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (ρ σ : Matrix Y Y' k → V →ₗ[ℂ] V) (hρ : ∀ x x' f, ρ x (ρ x' f) = ρ (x + x') f)
    (hσ : ∀ x x' f, σ x (σ x' f) = σ (x + x') f) (ρ0 : ∀ f, ρ 0 f = f) (σ0 : ∀ f, σ 0 f = f)
    (hc : ∀ x y f, ρ x (σ y f) = pairing ψ x y • σ y (ρ x f)) (P : Submodule ℂ V)
    (hP : ∀ x, ∀ f ∈ P, ρ x f ∈ P) (hP' : ∀ y, ∀ f ∈ P, σ y f ∈ P)
    (sm : ∀ f ∈ P, ∀ᶠ x in 𝓝 0, ρ x f = f) (sm' : ∀ f ∈ P, ∀ᶠ x in 𝓝 0, σ x f = f) {f : V} (hf : f ∈ P) (f0 : f ≠ 0) :
    ∃ g ∈ P, g ≠ 0 ∧ (∀ x ∈ box Y Y' (1 : kˣ), ρ x g = g) ∧
      ∀ y, (∀ x ∈ box Y Y' (1 : kˣ), pairing ψ x y = 1) → σ y g = g := by
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hb := isBichar_pairing (Y := Y) (Y' := Y') ψ
  obtain ⟨a, ha⟩ := exists_box_subset (sm f hf)
  haveI := finite_box (Y := Y) (Y' := Y') 1 a
  obtain ⟨g, hg, g0, hg1⟩ := exists_fixed hb ρ σ hρ
    (fun y f h => by rw [← σ0 f, ← neg_add_cancel y, ← hσ, h, map_zero]) hc (box Y Y' 1) (box Y Y' a)
    (fun u _ hu => let ⟨y, hy, hne⟩ := exists_sep hd a hu; ⟨y, fun κ hκ => pairing_box hd hκ hy, hne⟩)
    P (fun u _ => hP u) hP' hf f0 ha
  obtain ⟨b, hb'⟩ := exists_box_subset (sm' g hg)
  haveI := finite_box (Y := Y) (Y' := Y') (d / 1) b
  let Q : Submodule ℂ V :=
    { carrier := {v | v ∈ P ∧ ∀ x ∈ box Y Y' (1 : kˣ), ρ x v = v}
      zero_mem' := ⟨P.zero_mem, fun _ _ => map_zero _⟩
      add_mem' := fun h h' => ⟨P.add_mem h.1 h'.1, fun x hx => by rw [map_add, h.2 x hx, h'.2 x hx]⟩
      smul_mem' := fun c _ h => ⟨P.smul_mem c h.1, fun x hx => by rw [map_smul, h.2 x hx]⟩ }
  have hb2 : IsBichar fun y x : Matrix Y Y' k => pairing ψ (-x) y :=
    ⟨fun a b y => hb.right _ _ _, fun a y z => by rw [neg_add, hb.left], fun y => hb.zero_right _,
      fun a => by rw [neg_zero, hb.zero_left]⟩
  obtain ⟨g', hg', g0', hg2⟩ := exists_fixed hb2 σ ρ hσ
    (fun y f h => by rw [← ρ0 f, ← neg_add_cancel y, ← hρ, h, map_zero])
    (fun y x f => by rw [hc, smul_smul, hb.neg_mul, one_smul]) (box Y Y' (d / 1)) (box Y Y' b)
    (fun u _ hu => by
      obtain ⟨y, hy, hne⟩ := exists_sep hd b hu
      refine ⟨-y, fun κ hκ => ?_, ?_⟩
      · rw [neg_neg, pairing_comm]
        exact pairing_box hd hκ hy
      · rwa [neg_neg, pairing_comm])
    Q (fun u hu v hv => ⟨hP' u v hv.1, fun x hx => by rw [hc, pairing_box hd hx hu, hv.2 x hx, one_smul]⟩)
    (fun y v hv => ⟨hP y v hv.1, fun x hx => by rw [hρ, add_comm, ← hρ, hv.2 x hx]⟩) ⟨hg, hg1⟩ g0 hb'
  refine ⟨g', hg'.1, g0', hg'.2, fun y hy => hg2 y ?_⟩
  by_contra hn
  obtain ⟨x, hx, hne⟩ := exists_sep hd _ hn
  rw [div_one, div_self'] at hx
  exact hne ((pairing_comm ψ y x).trans (hy x hx))
end GlobalTheory.LocMod.Inhab
