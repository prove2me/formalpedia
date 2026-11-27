-- Prove2me | solution 1 for GlobalTheory.TwistTie.det_sub_mem_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:38:26.157185+00:00
-- url     : https://prove2.me/submissions/f29bc541-e958-4b13-a5b7-25f6edaaffb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_DetSubMemOfConj
import Theorems.Thm_GlobalTheory_TwistTie_det_sub_mem_of_conj
import Theorems.Thm_GlobalTheory_AdLat_mul_mem_adelicCompletionOfElementSet_of_mul_mem
import Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_tmul_mem_adelicCompletion_of_integral
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_smul_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TwistTie
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.TwistTie
theorem _root_.solution {n : ℕ} {La : Type} [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La]
    (ι : La →ₗ[𝓞 E] (Fin n → E)) (hsp : Submodule.span E (Set.range ι) = ⊤) (I : Ideal (𝓞 E)) (hI : I ≠ ⊤)
    (v : Fin n → La) (hv : (⊤ : Submodule (𝓞 E) La) ≤ Submodule.span (𝓞 E) (Set.range v) ⊔ I • ⊤)
    (s : La →ₗ[𝓞 E] La) (N : ℕ) (hN : (N : 𝓞 E) ∈ I) (G : Matrix (Fin n) (Fin n) (RA F E))
    (hG : G.det ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (h : ∀ j, ∃ w ∈ hat F (Set.range ι), G *ᵥ fv F (ι (v j)) - fv F (ι (s (v j))) = N • w) :
    ∃ a : Matrix (Fin n) (Fin n) (𝓞 E), (∀ j, s (v j) - ∑ i, a i j • v i ∈ (I • ⊤ : Submodule (𝓞 E) La)) ∧
      G.det - 1 ⊗ₜ ((a.det : 𝓞 E) : E) ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E))) := by
  obtain ⟨t, ht1, ht⟩ : ∃ t : 𝓞 E, t - 1 ∈ I ∧ ∀ l : La, t • l ∈ Submodule.span (𝓞 E) (Set.range v) := by
    obtain ⟨t, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
      (⊤ : Submodule (𝓞 E) (La ⧸ Submodule.span (𝓞 E) (Set.range v))) Module.Finite.fg_top (by
        intro q _
        obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (hv (Submodule.mem_top : l ∈ ⊤))
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hu, zero_add]
        refine Submodule.smul_induction_on hv (fun a ha z _ => ?_) (fun u v hu hv => ?_)
        · rw [Submodule.Quotient.mk_smul]; exact Submodule.smul_mem_smul ha trivial
        · rw [Submodule.Quotient.mk_add]; exact add_mem hu hv)
    refine ⟨t, hs1, fun l => ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact hs _ trivial
  have ht0 : (t : E) ≠ 0 := by
    rw [RingOfIntegers.coe_ne_zero_iff]
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using ht1
  choose co hco using fun l => (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (ht l)
  let P₀ : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => ι (v j) i
  have hP₀ : ∀ l, P₀ *ᵥ (fun j => (co l j : E)) = (t : E) • ι l := fun l => by
    have := congrArg ι (hco l)
    rw [map_sum, map_smul] at this
    funext i
    have := congrFun this i
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, Algebra.smul_def] at this
    simp only [P₀, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    exact (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans this
  have hu : IsUnit P₀ := by
    refine Matrix.mulVec_surjective_iff_isUnit.1 ?_
    have : LinearMap.range P₀.mulVecLin = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      refine ⟨(t : E)⁻¹ • fun j => (co l j : E), ?_⟩
      rw [map_smul, Matrix.mulVecLin_apply, hP₀, inv_smul_smul₀ ht0]
    exact LinearMap.range_eq_top.1 this
  let inc : E →+* RA F E := (Algebra.TensorProduct.includeRight (R := F)).toRingHom
  have hinc : ∀ x, inc x = 1 ⊗ₜ x := fun _ => rfl
  let f : 𝓞 E →+* RA F E := inc.comp (algebraMap _ _)
  have hfv : ∀ x : Fin n → E, fv F x = fun i => inc (x i) := fun _ => rfl
  have hf : ∀ x, f x ∈ intRing F := fun x => one_tmul_mem_adelicCompletionOfElementSet F ⟨x, rfl⟩
  have hPl : ∀ l, P₀.map inc *ᵥ (fun j => f (co l j)) = f t • fv F (ι l) := fun l => by
    funext i
    have := congrArg inc (congrFun (hP₀ l) i)
    rw [RingHom.map_mulVec, Pi.smul_apply, smul_eq_mul, map_mul] at this
    exact this
  have hw : ∀ w ∈ hat F (Set.range ι), ∃ y : Fin n → RA F E, (∀ i, y i ∈ intRing F) ∧ P₀.map inc *ᵥ y = f t • w := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, _, ⟨l, rfl⟩, rfl⟩ := hx
      refine ⟨(b ⊗ₜ[F] (1 : E) : RA F E) • fun j => f (co l j),
        fun i => mul_mem (tmul_mem_adelicCompletion_of_integral F hb ⟨1, map_one _⟩ : _ ∈ intRing F) (hf _), ?_⟩
      rw [Matrix.mulVec_smul, hPl, smul_comm]
      congr 1
      funext i
      simp [fv]
    | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', ex⟩ := hx
      obtain ⟨y', hy', ey⟩ := hy
      exact ⟨x' + y', fun i => add_mem (hx' i) (hy' i), by rw [Matrix.mulVec_add, ex, ey, smul_add]⟩
    | neg x _ hx =>
      obtain ⟨x', hx', ex⟩ := hx
      exact ⟨-x', fun i => neg_mem (hx' i), by rw [Matrix.mulVec_neg, ex, smul_neg]⟩
  choose w hwm hwe using h
  choose y hy hye using fun j => hw _ (hwm j)
  refine ⟨Matrix.of fun i j => co (s (v j)) i, fun j => ?_, ?_⟩
  · simp only [Matrix.of_apply]
    rw [hco, show s (v j) - t • s (v j) = -((t - 1) • s (v j)) by rw [sub_smul, one_smul, neg_sub]]
    exact neg_mem (Submodule.smul_mem_smul ht1 trivial)
  · refine det_sub_mem_of_conj f (intRing F) hf I _ (fun x hx z hz => ?_) G (P₀.map inc) (Matrix.of fun i j => y j i) _ t N
      ht1 hN ?_ hG (fun i j => hy j i) ?_
    · exact mul_mem_adelicCompletionOfElementSet_of_mul_mem F (I := algebraMap (𝓞 E) E '' (I : Set (𝓞 E)))
        (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, I.mul_mem_right _ hx, map_mul _ _ _⟩)
        (one_tmul_mem_adelicCompletionOfElementSet F ⟨x, hx, rfl⟩) hz
    · exact (Matrix.isUnit_iff_isUnit_det _).1 (hu.map inc.mapMatrix)
    · ext i j
      have e1 : ((f t • G) * P₀.map inc) i j = (f t • (G *ᵥ fv F (ι (v j)))) i := by
        rw [Matrix.smul_mul]; rfl
      have e2 : (P₀.map inc * ((Matrix.of fun i j => co (s (v j)) i).map f + f N • Matrix.of fun i j => y j i)) i j =
          (P₀.map inc *ᵥ ((fun i => f (co (s (v j)) i)) + f N • y j)) i := rfl
      rw [e1, e2, Matrix.mulVec_add, Matrix.mulVec_smul, hPl, hye, sub_eq_iff_eq_add'.1 (hwe j), smul_add, map_natCast,
        Nat.cast_smul_eq_nsmul, smul_comm]
end GlobalTheory.TwistTie
