-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.exists_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:00:28.485989+00:00
-- url     : https://prove2.me/submissions/ead904e1-8862-47da-84ee-0454afef896c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_InvariantOfTsupport
import Theorems.Thm_P2M_GlobalTheory_LocMod_Inhab_exists_map_wave__4bfad06d87ba
import Theorems.Thm_GlobalTheory_LocMod_Inhab_sb_le
import Theorems.Thm_GlobalTheory_LocMod_Inhab_ind_box_mem
import Theorems.Thm_GlobalTheory_LocMod_Inhab_exists_sep
import Theorems.Thm_GlobalTheory_LocMod_Inhab_isBichar_pairing
import Theorems.Thm_GlobalTheory_LocMod_Inhab_pairing_box
import Theorems.Thm_GlobalTheory_LocMod_Inhab_pairing_comm
import Theorems.Thm_GlobalTheory_PlaceModel_IsBichar_neg_mul
import Theorems.Thm_GlobalTheory_PlaceModel_modul_mem
import Theorems.Thm_GlobalTheory_PlaceModel_trans_mem
import Theorems.Thm_GlobalTheory_PlaceModel_wave_modul
import Theorems.Thm_GlobalTheory_PlaceModel_wave_trans
import Theorems.Thm_GlobalTheory_PlaceModel_wave_zero
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
    (hσ : ∀ x x' f, σ x (σ x' f) = σ (x + x') f)
    (hc : ∀ x y f, ρ x (σ y f) = pairing ψ x y • σ y (ρ x f)) (P : Submodule ℂ V)
    (hP : ∀ x, ∀ f ∈ P, ρ x f ∈ P) (hP' : ∀ y, ∀ f ∈ P, σ y f ∈ P) {g : V} (hg : g ∈ P) (g0 : g ≠ 0)
    (hg1 : ∀ x ∈ box Y Y' (1 : kˣ), ρ x g = g)
    (hg2 : ∀ y, (∀ x ∈ box Y Y' (1 : kˣ), pairing ψ x y = 1) → σ y g = g) :
    ∃ T : (Matrix Y Y' k → ℂ) →ₗ[ℂ] V, ∀ Φ ∈ SB (Matrix Y Y' k), (T Φ = 0 → Φ = 0) ∧ T Φ ∈ P ∧
      (∀ x, T (fun t => Φ (t + x)) = ρ x (T Φ)) ∧ ∀ y, T (fun t => pairing ψ t y * Φ t) = σ y (T Φ) := by
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hb := isBichar_pairing (Y := Y) (Y' := Y') ψ
  obtain ⟨T, hT⟩ := exists_map_wave₂ hb (L := box Y Y' 1) (L' := box Y Y' (d / 1))
    (fun u hu y hy => pairing_box hd hu hy)
    (fun y hy => by_contra fun hn => by
      obtain ⟨x, hx, hne⟩ := exists_sep hd _ hn
      rw [div_one, div_self'] at hx
      exact hne ((pairing_comm ψ y x).trans (hy x hx)))
    ρ σ hρ hσ hc g hg1 fun u hu => hg2 u fun x hx => pairing_box hd hx hu
  have h0 : T (ind (box Y Y' 1)) = g := by
    rw [← wave_zero hb, hT, hg2 0 fun x _ => hb.zero_right x, hg1 0 (zero_mem _)]
  have hne : ind (box Y Y' (1 : kˣ)) ≠ 0 := fun e => g0 (by rw [← h0, e, map_zero])
  have key : ∀ Φ ∈ waveSpan (pairing ψ) ⊤ ⊤ (box Y Y' (1 : kˣ)), T Φ ∈ P ∧
      (∀ x, T (fun t => Φ (t + x)) = ρ x (T Φ)) ∧ ∀ y, T (fun t => pairing ψ t y * Φ t) = σ y (T Φ) := fun Φ hΦ => by
    induction hΦ using Submodule.span_induction with
    | mem _ hh =>
      obtain ⟨a, -, b, -, rfl⟩ := hh
      refine ⟨hT a b ▸ hP _ _ (hP' _ _ hg), fun x => ?_, fun y => ?_⟩
      · rw [wave_trans, hT, hT, hρ]
      · rw [wave_modul hb, map_smul, hT, hT, ← hσ, hc a y, smul_smul, hb.neg_mul, one_smul]
    | zero =>
      refine ⟨by rw [map_zero]; exact P.zero_mem, fun x => ?_, fun y => ?_⟩
      · rw [map_zero, map_zero]; exact map_zero T
      · rw [map_zero, map_zero, ← map_zero T]; congr 1; funext t; simp
    | add f g _ _ hf hg =>
      refine ⟨by rw [map_add]; exact P.add_mem hf.1 hg.1, fun x => ?_, fun y => ?_⟩
      · rw [map_add, map_add, ← hf.2.1 x, ← hg.2.1 x, ← map_add]; rfl
      · rw [map_add, map_add, ← hf.2.2 y, ← hg.2.2 y, ← map_add]; congr 1; funext t; simp [mul_add]
    | smul c f _ hf =>
      refine ⟨by rw [map_smul]; exact P.smul_mem c hf.1, fun x => ?_, fun y => ?_⟩
      · rw [map_smul, map_smul, ← hf.2.1 x, ← map_smul]; rfl
      · rw [map_smul, map_smul, ← hf.2.2 y, ← map_smul]; congr 1; funext t; simp [mul_left_comm]
  have hle : SB (Matrix Y Y' k) ≤ waveSpan (pairing ψ) ⊤ ⊤ (box Y Y' (1 : kˣ)) :=
    sb_le hd (fun x _ h => trans_mem h trivial) (fun y _ h => modul_mem hb h trivial) (ind_box_mem 1) hne
      (Submodule.subset_span ⟨0, trivial, 0, trivial, (wave_zero hb).symm⟩)
  refine ⟨T, fun Φ hΦ => ⟨fun hz => by_contra fun hn => g0 ?_, key Φ (hle hΦ)⟩⟩
  have := sb_le hd (N := waveSpan (pairing ψ) ⊤ ⊤ (box Y Y' (1 : kˣ)) ⊓ LinearMap.ker T)
    (fun x Ψ h => ⟨trans_mem h.1 trivial, by
      change T _ = 0
      rw [(key Ψ h.1).2.1, show T Ψ = 0 from h.2, map_zero]⟩)
    (fun y Ψ h => ⟨modul_mem hb h.1 trivial, by
      change T _ = 0
      rw [(key Ψ h.1).2.2, show T Ψ = 0 from h.2, map_zero]⟩) hΦ hn ⟨hle hΦ, hz⟩ (ind_box_mem 1)
  rw [← h0]
  exact this.2
end GlobalTheory.LocMod.Inhab
