-- Prove2me | solution 1 for GlobalTheory.PrimeOrderScalar.acts_by_same_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:47:53.259002+00:00
-- url     : https://prove2.me/submissions/1df4839b-c9f2-4616-b469-0fba93538c2c

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_zsmul_eq_zero_iff
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_not_isUnit_of_kills
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_same_int_of_local
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_same_int_of_mul
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_coe_inclO
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_inclW_algebraMap
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_isUnit_algebraMap
import Theorems.Thm_GlobalTheory_PrimeOrderScalar_sub_kill_eq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open GlobalTheory GlobalTheory.PrimeOrderScalar
open scoped TensorProduct
namespace GlobalTheory.PrimeOrderScalar
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)), (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → ∀ (T : ℕ), T.Prime → (T : 𝓞 F) ∈ w.asIdeal → ∀ (p : 𝓞 E), (∀ d : 𝓞 F, algebraMap F E (d : F) = (p : E) + σ (p : E) → d ∉ w.asIdeal) → ∀ (A B : Type) [AddCommGroup A] [Module (intV E w) A] [AddCommGroup B] [Module (intV E w) B], Nat.card A = T → Nat.card B = T → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : A, a • m = 0) → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : B, a • m = 0) → ∀ s : intV E w, ∃ k : ℤ, (∀ m : A, s • m = k • m) ∧ ∀ m : B, s • m = k • m := by
  intro F E _ _ _ _ _ σ w hinv hfix T hT hTw p hd A B _ _ _ _ hA hB hpA hpB s
  let Q : intV E w → Prop := fun s =>
    ∃ k : ℤ, (∀ m : A, s • m = k • m) ∧ ∀ m : B, s • m = k • m
  have hadd : ∀ a b, Q a → Q b → Q (a + b) := by
    rintro a b ⟨k1, h1A, h1B⟩ ⟨k2, h2A, h2B⟩
    exact ⟨k1 + k2, fun m => by rw [add_smul, add_smul, h1A, h2A],
      fun m => by rw [add_smul, add_smul, h1B, h2B]⟩
  have hmul : ∀ a b, Q a → Q b → Q (a * b) := by
    rintro a b ⟨k1, h1A, h1B⟩ ⟨k2, h2A, h2B⟩
    refine ⟨k1 * k2, fun m => ?_, fun m => ?_⟩
    · rw [mul_smul, h2A, smul_comm, h1A, smul_smul, mul_comm]
    · rw [mul_smul, h2B, smul_comm, h1B, smul_smul, mul_comm]
  have hneg : ∀ a, Q a → Q (-a) := by
    rintro a ⟨k, hkA, hkB⟩
    exact ⟨-k, fun m => by rw [neg_smul, neg_smul, hkA], fun m => by rw [neg_smul, neg_smul, hkB]⟩
  have h0 : Q 0 := ⟨0, fun m => by simp, fun m => by simp⟩
  have h1 : Q 1 := ⟨1, fun m => by simp, fun m => by simp⟩
  have hW : ∀ y, Q (inclW w y) := fun y => same_int_of_local (inclW w) hT hA hB y
  have hσint : ∀ o : 𝓞 E, IsIntegral ℤ (σ (o : E)) := fun o => map_isIntegral_int σ o.2
  let σO : 𝓞 E → 𝓞 E := fun o => ⟨σ (o : E), hσint o⟩
  have hdesc : ∀ e : E, IsIntegral ℤ e → σ e = e → ∃ f : 𝓞 F, algebraMap F E (f : F) = e := by
    intro e he hσe
    obtain ⟨f, hf⟩ := hfix e hσe
    have hfi : IsIntegral ℤ f :=
      (isIntegral_algebraMap_iff (algebraMap F E).injective).mp (hf ▸ he)
    exact ⟨⟨f, hfi⟩, hf⟩
  have hE : ∀ o : 𝓞 E, Q (inclO w o) := by
    intro o
    obtain ⟨d', hd'⟩ := hdesc ((p : E) + σ p) (IsIntegral.add p.2 (hσint p))
      (by rw [map_add, hinv, add_comm])
    obtain ⟨c', hc'⟩ := hdesc ((o : E) * σ p + σ o * p)
      (IsIntegral.add (IsIntegral.mul o.2 (hσint p)) (IsIntegral.mul (hσint o) p.2))
      (by rw [map_add, map_mul, map_mul, hinv, hinv]; ring)
    obtain ⟨δ, hδA, hδB⟩ := hW (algebraMap (𝓞 F) _ d')
    obtain ⟨γ, hγA, hγB⟩ := hW (algebraMap (𝓞 F) _ c')
    have hD : inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d') =
        inclO w p + inclO w (σO p) := by
      rw [← map_add]
      apply Subtype.ext
      rw [inclW_algebraMap, coe_inclO, hd']
      rfl
    have hC : inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) c') =
        inclO w o * inclO w (σO p) + inclO w (σO o) * inclO w p := by
      rw [← map_mul, ← map_mul, ← map_add]
      apply Subtype.ext
      rw [inclW_algebraMap, coe_inclO, hc']
      rfl
    have hPA : ∀ m : A, inclO w p • m = 0 := hpA _ rfl
    have hPB : ∀ m : B, inclO w p • m = 0 := hpB _ rfl
    have hXA : ∀ m : A, inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d') • inclO w o • m =
        inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) c') • m := by
      intro m
      rw [← mul_smul, hD, hC]
      exact sub_kill_eq _ _ _ _ hPA m
    have hXB : ∀ m : B, inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d') • inclO w o • m =
        inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) c') • m := by
      intro m
      rw [← mul_smul, hD, hC]
      exact sub_kill_eq _ _ _ _ hPB m
    have hδ : ¬ (T : ℤ) ∣ δ := fun h =>
      not_isUnit_of_kills hT hA (u := inclW w (algebraMap (𝓞 F) _ d'))
        (fun m => by rw [hδA]; exact (zsmul_eq_zero_iff hT hA δ).mpr h m)
        ((isUnit_algebraMap w d' (hd d' hd')).map _)
    exact same_int_of_mul hT hA hB _ _ _ δ γ hδA hδB hγA hγB hXA hXB hδ
  have key : ∀ z (hz : z ∈ intV E w), Q ⟨z, hz⟩ := by
    intro z hz
    refine Subring.closure_induction (p := fun z hz => Q ⟨z, hz⟩) ?_ h0 h1
      (fun x y hx hy qx qy => hadd _ _ qx qy) (fun x hx qx => hneg _ qx)
      (fun x y hx hy qx qy => hmul _ _ qx qy) hz
    rintro x (⟨⟨_, o, rfl⟩, rfl⟩ | ⟨y, rfl⟩)
    · exact hE o
    · exact hW ⟨y.1, y.2⟩
  exact key s.1 s.2
end GlobalTheory.PrimeOrderScalar
