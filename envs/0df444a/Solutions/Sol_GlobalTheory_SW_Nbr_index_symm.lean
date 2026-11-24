-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.index_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:58:41.586895+00:00
-- url     : https://prove2.me/submissions/ebd7856f-992d-476a-9bba-490212f76bfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_good_conj
import Theorems.Thm_GlobalTheory_SW_Nbr_ne_bot_of_norm
import Theorems.Thm_GlobalTheory_SW_Nbr_max_of_norm
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e
import Theorems.Thm_GlobalTheory_SW_Nbr_SD_eq_of_le
import Theorems.Thm_GlobalTheory_SW_Nbr_smul_le_iff
import Theorems.Thm_GlobalTheory_SW_Nbr_conj_le
import Theorems.Thm_GlobalTheory_SW_Nbr_relIndex_eq
import Theorems.Thm_GlobalTheory_SW_Nbr_exists_not_mem
import Theorems.Thm_GlobalTheory_SW_Hyper_cyc_of_prime
import Theorems.Thm_GlobalTheory_SW_Hyper_exists_fun
import Theorems.Thm_GlobalTheory_SW_Hyper_index_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.Nbr
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ' : Lt E n}
    (hS : SD Λ) (hS' : SD Λ') (hle : P • Λ ≤ Λ')
    (hi : Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup = q) :
    Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup = q := by
  have hQ := good_conj hP
  have hmax := max_of_norm hQ.1 hQ.2.2.1
  have hle' := smul_le_iff.1 (conj_le hS hS' hle)
  obtain ⟨v, hv, hc⟩ := Hyper.cyc_of_prime (Λ'.comap Λ.subtype) hP.1 hi
  have key : ∀ x ∈ Λ', x ∈ Λ ↔ Int' x v := fun x hx => ⟨fun h => (hS x).1 h v v.2, fun h =>
    (hS x).2 fun y hy => by
      obtain ⟨r, hr⟩ := hc ⟨y, hy⟩
      have hr : y - r • (v : Fin n → E) ∈ Λ' := hr
      have := ((hS' _).1 hr x hx).add (h.symm.smul r)
      rw [sub_add_cancel] at this
      exact this.symm⟩
  obtain ⟨w, hw, hw'⟩ : ∃ w ∈ Λ', w ∉ Λ := by
    by_contra hn
    push Not at hn
    exact hv (show (v : Fin n → E) ∈ Λ' from (hS'.eq_of_le hS hn).ge v.2)
  have hint : ∀ x ∈ Λ', ∀ d ∈ conjI P, IsIntegral ℤ ((d : E) * herm 1 x v) := fun x hx d hd => by
    rw [← herm_sl]
    exact (hS _).1 (hle' d hd x hx) v v.2
  obtain ⟨d, hd, r, hr, hrd⟩ := exists_not_mem (ne_bot_of_norm hQ.1 hQ.2.2.1)
    (fun h => hw' ((key w hw).2 h)) (hint w hw)
  obtain ⟨u, c, hc, huc⟩ := hmax.exists_inv hr
  have h3 : (u : E) * (r : E) + (c : E) = 1 := by exact_mod_cast congrArg (fun a : 𝓞 E => (a : E)) huc
  obtain ⟨f, hf, hk⟩ := Hyper.exists_fun (conjI P) (Λ.comap Λ'.subtype) ⟨w, hw⟩ hw'
    (fun c hc => hle' c hc w hw) fun x => by
      let e : 𝓞 E := ⟨_, hint x x.2 d hd⟩
      refine ⟨u * e, (key _ (x - (u * e) • (⟨w, hw⟩ : Λ')).2).2 ?_⟩
      have h4 : herm 1 ((x : Fin n → E) - (u * e) • w) v = (c : E) * herm 1 (x : Fin n → E) v := by
        rw [sub_eq_add_neg, ← neg_smul, herm_al, osmul, herm_sl]
        have : ((-(u * e) : 𝓞 E) : E) = -((u : E) * ((d : E) * herm 1 (x : Fin n → E) v)) := rfl
        rw [this]
        linear_combination (-herm 1 (x : Fin n → E) v) * h3 + (u : E) * herm 1 (x : Fin n → E) v * hrd
      show IsIntegral ℤ (herm 1 ((x : Fin n → E) - (u * e) • w) v)
      rw [h4]
      exact hint x x.2 c hc
  rw [relIndex_eq, ← hk, Hyper.index_ker _ f hf]
  exact hQ.2.2.1
end GlobalTheory.SW.Nbr
