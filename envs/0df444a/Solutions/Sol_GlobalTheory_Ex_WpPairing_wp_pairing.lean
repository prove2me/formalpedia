-- Prove2me | solution 1 for GlobalTheory.Ex.WpPairing.wp_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:39.166547+00:00
-- url     : https://prove2.me/submissions/5399675f-39da-4ad9-8afa-079652bf3710

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingProperties
import Theorems.Thm_GlobalTheory_Ex_WpPairing_wp_pow_left
import Theorems.Thm_GlobalTheory_Ex_WpPairing_wp_qTriv
import Theorems.Thm_GlobalTheory_Ex_WpPairing_wp_congr_left
import Theorems.Thm_GlobalTheory_Ex_NumD_exists_tor_iff
import Theorems.Thm_GlobalTheory_Ex_NumD_tor_injective
import Theorems.Thm_GlobalTheory_Ex_NumD_wp_of_eq_zero
import Theorems.Thm_GlobalTheory_Ex_NumD_wp_self
import Theorems.Thm_GlobalTheory_Ex_NumD_wp_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.WpPairing
variable {O : Type} [CommRing O] (N : NumD O)
open scoped BigOperators
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O)
namespace GlobalTheory.Ex.WpPairing
namespace _root_.GlobalTheory.Ex.WpPairing
theorem _root_.solution : ∀ (O : Type) [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O), ∀ (k : ℕ) (p p' p'' : N.QT k), N.wp (p * p') p'' = N.wp p p'' * N.wp p' p'' ∧ N.wp p p = 1 ∧ N.wp p p' * N.wp p' p = 1 ∧ N.wp p p' ^ k = 1 ∧ (N.QEq p p' → N.wp p p'' = N.wp p' p'') ∧ (p.1.1 = 1 → p.1.2.b = 1 → N.wp p p' = p.1.2.s p'.1.1.toAdd) ∧ (p.1.1 = 1 → p'.1.1 = 1 → N.wp p p' = N.weil k p.1.2.b p'.1.2.b) := by
  intro O _ N k p p' p''
  refine ⟨_root_.GlobalTheory.Ex.WpPairing.wp_mul_left N p p' p'', N.wp_self p, ?_, ?_,
    fun h => _root_.GlobalTheory.Ex.WpPairing.wp_congr_left N h p'', ?_,
    fun h1 h2 => N.wp_of_eq_zero p p' (by simp [h1]) (by simp [h2])⟩
  · rw [N.wp_swap p p', mul_inv_cancel]
  · have hp : p ^ k = N.qTriv k
        (Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1) := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, _root_.GlobalTheory.Ex.NumD.qTriv]
      refine Prod.ext ?_ ?_
      · simp
      · simpa using N.mem_QT.mp p.2
    rw [← _root_.GlobalTheory.Ex.WpPairing.wp_pow_left, hp, _root_.GlobalTheory.Ex.WpPairing.wp_qTriv]
  · intro h1 hb
    obtain ⟨t, ht⟩ := (N.exists_tor_iff _).mpr hb
    have hk := N.mem_QT.mp p.2
    rw [h1, toAdd_one, N.io_zero] at hk
    have htk : t ^ k = 1 := N.tor_injective (by rw [N.tor_pow, ht, N.tor_one, hk])
    have hp : p = N.qTor t htk := by
      apply Subtype.ext
      simp only [_root_.GlobalTheory.Ex.NumD.qTor]
      exact Prod.ext h1 ht.symm
    calc N.wp p p' =
          N.wp (N.qTor t htk) p' := by
          rw [← hp]
      _ = t (p' : Multiplicative N.X × N.Gt).1 := N.wp_qTor t htk p'
      _ = _ := by rw [← ht, N.torus_generator_apply, ofAdd_toAdd]
end _root_.GlobalTheory.Ex.WpPairing
end GlobalTheory.Ex.WpPairing
