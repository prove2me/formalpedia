-- Prove2me | solution 1 for GlobalTheory.PadicH2Separated.mem_coboundaries_of_forall_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:51:46.206365+00:00
-- url     : https://prove2.me/submissions/795320bd-9fdc-431e-98c1-548a06109d60

import Mathlib
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicCoboundaryOfDivisible
import Theorems.Thm_GlobalTheory_PadicH2Separated_continuous_reduction
import Theorems.Thm_GlobalTheory_PadicH2Separated_continuous_of_reductions
import Theorems.Thm_GlobalTheory_PadicH2Separated_finite_primitives
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
open GlobalTheory GlobalTheory.PadicH2Separated
namespace GlobalTheory.PadicH2Separated
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]) (ρr : ∀ r : ℕ, Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ r g x, PadicInt.toZModPow r (ρ g x) = ρr r g (PadicInt.toZModPow r x)) → (∀ r, 0 < r → Finite (H1 (ρr r))) → ∀ z ∈ Z2 ρ, (∀ r : ℕ, ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ) → z ∈ B2 ρ := by
  intro l _ Γ _ _ ρ ρr hρ hfin z _ hz
  have hd : ∀ (s : ℕ) (b : Γ → ℤ_[l]), d1 (ρr s) (fun g => PadicInt.toZModPow s (b g)) =
      fun p => PadicInt.toZModPow s (d1 ρ b p) := by
    intro s b
    funext ⟨g, h⟩
    simp only [d1_apply, map_add, map_sub, hρ]
  let α : ∀ s : ℕ, Set (Γ → ZMod (l ^ s)) := fun s =>
    {β | Continuous β ∧ d1 (ρr s) β = fun p => PadicInt.toZModPow s (z p)}
  have hα : ∀ s, (α (s + 1)).Finite := by
    intro s
    haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    haveI := hfin (s + 1) (Nat.succ_pos s)
    exact finite_primitives (ρr (s + 1)) _
  let T : ℕ → Set (Γ → ℤ_[l]) := fun r =>
    ⋂ s, ⋂ (_ : s ≤ r), (fun (b : Γ → ℤ_[l]) g => PadicInt.toZModPow (s + 1) (b g)) ⁻¹' α (s + 1)
  have hcl : ∀ r, IsClosed (T r) := fun r =>
    isClosed_iInter fun s => isClosed_iInter fun _ => (hα s).isClosed.preimage
      (continuous_pi fun g => (continuous_reduction _).comp (continuous_apply g))
  have hne : ∀ r, (T r).Nonempty := by
    intro r
    obtain ⟨w, -, c, hc, hcd⟩ := hz (r + 1)
    refine ⟨c, Set.mem_iInter₂.2 fun s hs => ⟨(continuous_reduction _).comp hc, ?_⟩⟩
    rw [hd, hcd]
    funext p
    have h0 : PadicInt.toZModPow (s + 1) ((l : ℤ_[l]) ^ (r + 1)) = 0 := by
      rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact pow_dvd_pow _ (by omega)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, h0, zero_mul, sub_zero]
  have hdec : ∀ r, T (r + 1) ⊆ T r := fun r b hb =>
    Set.mem_iInter₂.2 fun s hs => Set.mem_iInter₂.1 hb s (hs.trans (Nat.le_succ r))
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  have hb' : ∀ s, (fun g => PadicInt.toZModPow (s + 1) (b g)) ∈ α (s + 1) := fun s =>
    Set.mem_iInter₂.1 (Set.mem_iInter.1 hb s) s le_rfl
  refine ⟨b, continuous_of_reductions b fun s => (hb' s).1, ?_⟩
  funext p
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    have := (hb' n).2
    rw [hd] at this
    exact congrFun this p
end GlobalTheory.PadicH2Separated
