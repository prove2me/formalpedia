-- Prove2me | solution 1 for GlobalTheory.LocSpan.mem_O_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:27.852274+00:00
-- url     : https://prove2.me/submissions/bc505e54-e850-431a-ab78-e309e8d680aa

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIntegersLocalisationIffSumCmData
import Theorems.Thm_GlobalTheory_LocSpan_exists_disc_notMem
import Theorems.Thm_GlobalTheory_LocSpan_exists_coord
import Theorems.Thm_P2M_GlobalTheory_LocSpan_isIntegral__E_a7279f9601bd
import Theorems.Thm_GlobalTheory_LocSpan_mem_integer_of_isIntegral
import Theorems.Thm_P2M_GlobalTheory_LocSpan_valuation__F_eq_one_aeca8e235b98
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LocSpan
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
namespace GlobalTheory.LocSpan
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p), ∀ y : A.Ep, y ∈ A.O ↔ ∃ (n : ℕ) (c : Fin n → 𝒪[A.Fp]) (x : Fin n → 𝓞 E), y = ∑ i, algebraMap A.Fp A.Ep (c i : A.Fp) * A.ιE (x i : E) := by
  intro F E _ _ _ _ _ _ hc sig hsig p A y
  constructor
  · intro hy
    rw [A.O_def] at hy
    obtain ⟨θ, t, d, ht, hd, hdisc⟩ := exists_disc_notMem hc p
    have hv := valuation_ιF_eq_one A d hd
    have hne : (θ : E) - star (θ : E) ≠ 0 := by
      intro h
      rw [ht, h] at hdisc
      have : d = 0 := by
        apply RingOfIntegers.ext
        simpa using hdisc
      exact hd (this ▸ p.asIdeal.zero_mem)
    have hco : ∀ z : A.Ep, ∃ a b : A.Fp,
        z = algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (θ : E) := by
      intro z
      have hz : z ∈ Submodule.span A.Fp (Set.range A.ιE) := by rw [A.span]; trivial
      induction hz using Submodule.span_induction with
      | mem _ hx =>
        obtain ⟨x, rfl⟩ := hx
        obtain ⟨a, b, rfl⟩ := exists_coord hc θ hne x
        exact ⟨A.ιF a, A.ιF b, by rw [map_add, map_mul, A.compat, A.compat]⟩
      | zero => exact ⟨0, 0, by simp⟩
      | add _ _ _ _ h1 h2 =>
        obtain ⟨a, b, rfl⟩ := h1
        obtain ⟨a', b', rfl⟩ := h2
        exact ⟨a + a', b + b', by rw [map_add, map_add]; ring⟩
      | smul c _ _ h1 =>
        obtain ⟨a, b, rfl⟩ := h1
        exact ⟨c * a, c * b, by rw [map_mul, map_mul, Algebra.smul_def]; ring⟩
    obtain ⟨a, b, rfl⟩ := hco y
    have hcj := hy.map (A.cj.toAlgHom.restrictScalars 𝒪[A.Fp])
    have hcj' : IsIntegral 𝒪[A.Fp]
        (algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (t : E)) := by
      have e : A.cj (algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (θ : E)) =
          algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (t : E) := by
        rw [map_add, map_mul, A.cj.commutes, A.cj.commutes, A.cj_ιE, hsig, ht]
      rw [← e]; exact hcj
    have hbd : b * A.ιF (d : F) ∈ 𝒪[A.Fp] := by
      apply mem_integer_of_isIntegral A
      have := (hy.sub hcj').mul ((isIntegral_ιE A θ).sub (isIntegral_ιE A t))
      convert this using 1
      rw [map_mul, ← A.compat, hdisc, map_pow, map_sub]; ring
    have hb : b ∈ 𝒪[A.Fp] := by
      rw [Valuation.mem_integer_iff] at hbd ⊢
      rwa [map_mul, hv, mul_one] at hbd
    have hbI : IsIntegral 𝒪[A.Fp] (algebraMap A.Fp A.Ep b) :=
      isIntegral_algebraMap (R := 𝒪[A.Fp]) (x := ⟨b, hb⟩)
    have ha : a ∈ 𝒪[A.Fp] := by
      apply mem_integer_of_isIntegral A
      have := hy.sub (hbI.mul (isIntegral_ιE A θ))
      simpa using this
    exact ⟨2, ![⟨a, ha⟩, ⟨b, hb⟩], ![1, θ], by simp [Fin.sum_univ_two]⟩
  · rintro ⟨n, c, x, rfl⟩
    rw [A.O_def]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ (isIntegral_ιE A _)
    exact isIntegral_algebraMap (R := 𝒪[A.Fp]) (x := c i)
end GlobalTheory.LocSpan
