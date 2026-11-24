-- Prove2me | solution 1 for GlobalTheory.SW.Dict.tauOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:24:31.537615+00:00
-- url     : https://prove2.me/submissions/a84034a5-f376-487f-a2ff-79c30d3e5470

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Theorems.Thm_GlobalTheory_SW_Dict_exists_emb_comb
import Theorems.Thm_GlobalTheory_SW_Dict_quad_tauOf

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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Dict
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable (Ψ : Finset (E →+* ℂ))
variable {Ψ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable (Ψ : Finset (E →+* ℂ))
variable {Ψ}
namespace GlobalTheory.SW.Dict
namespace _root_.GlobalTheory.SW.Dict
theorem _root_.solution (hΨ : _root_.GlobalTheory.SW.IsType Ψ)
    (Z : _root_.GlobalTheory.SW.CM Ψ N N) (hZ : Z ∈ _root_.GlobalTheory.SW.Hn Ψ N) :
    _root_.GlobalTheory.SW.tauOf Ψ Z ∈ _root_.GlobalTheory.SW.Siegel (_root_.GlobalTheory.SW.QI E N) := by
  have hinv : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
    fun φ => by ext y; simp [ComplexEmbedding.conjugate_coe_eq]
  refine ⟨Matrix.IsSymm.ext fun p q => ?_, ?_⟩
  · simp only [_root_.GlobalTheory.SW.tauOf, Matrix.of_apply]
    exact Finset.sum_congr rfl fun _ _ => add_comm _ _
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨Matrix.IsHermitian.ext fun p q => ?_, fun x hx => ?_⟩
  · simp only [Matrix.map_apply, star_trivial, _root_.GlobalTheory.SW.tauOf, Matrix.of_apply]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => add_comm _ _
  rw [star_trivial]
  set m : _root_.GlobalTheory.SW.QI E N → ℂ := fun p => (x p : ℂ) with hmdef
  have hm : ∀ p, conj (m p) = m p := fun p => Complex.conj_ofReal _
  have hid : x ⬝ᵥ (_root_.GlobalTheory.SW.tauOf Ψ Z).map Complex.im *ᵥ x =
      (m ⬝ᵥ _root_.GlobalTheory.SW.tauOf Ψ Z *ᵥ m).im := by
    simp only [m, dotProduct, mulVec, Matrix.map_apply, Complex.im_sum, Complex.im_ofReal_mul,
      Complex.im_mul_ofReal]
  rw [hid, _root_.GlobalTheory.SW.Dict.quad_tauOf Ψ Z m hm]
  set v := fun τ : Ψ => _root_.GlobalTheory.SW.Dict.vec τ.1 m with hvdef
  have hterm : ∀ τ : Ψ, (v τ ⬝ᵥ Z τ *ᵥ fun a => conj (v τ a)).im =
      (star (fun a => conj (v τ a)) ⬝ᵥ _root_.GlobalTheory.SW.imH (Z τ) *ᵥ
        fun a => conj (v τ a)).re := by
    intro τ
    have hstar : star (fun a => conj (v τ a)) = v τ := by
      funext a; simp
    have hconjT : v τ ⬝ᵥ (Z τ)ᴴ *ᵥ (fun a => conj (v τ a)) =
        conj (v τ ⬝ᵥ Z τ *ᵥ fun a => conj (v τ a)) := by
      simp only [dotProduct, mulVec, conjTranspose_apply, map_sum, map_mul, Complex.star_def,
        Complex.conj_conj, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hstar]
    unfold _root_.GlobalTheory.SW.imH
    rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub, hconjT,
      Complex.sub_conj, smul_eq_mul]
    all_goals simp [Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq]
    all_goals field_simp
  have hpos : ∀ τ : Ψ, v τ ≠ 0 → 0 < (v τ ⬝ᵥ Z τ *ᵥ fun a => conj (v τ a)).im := by
    intro τ hv
    have hw : (fun a => conj (v τ a)) ≠ 0 := by
      intro h0
      apply hv
      funext a
      have := congrFun h0 a
      simpa using this
    have := (hZ τ).dotProduct_mulVec_pos hw
    rw [hterm]
    exact (Complex.lt_def.mp this).1
  have hnonneg : ∀ τ : Ψ, 0 ≤ (v τ ⬝ᵥ Z τ *ᵥ fun a => conj (v τ a)).im := by
    intro τ
    by_cases hv : v τ = 0
    · rw [hv]; simp
    · exact (hpos τ hv).le
  have hex : ∃ τ : Ψ, v τ ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hall : ∀ σ : E →+* ℂ, ∀ a, ∑ j, σ (Module.finBasis ℚ E j) * m (a, j) = 0 := by
      intro σ a
      by_cases hσ : σ ∈ Ψ
      · exact congrFun (hne ⟨σ, hσ⟩) a
      · have hc : ComplexEmbedding.conjugate σ ∈ Ψ := by
          have := (hΨ (ComplexEmbedding.conjugate σ)).mpr
          rw [hinv] at this
          exact this hσ
        have h1 := congrFun (hne ⟨_, hc⟩) a
        simp only [hvdef, _root_.GlobalTheory.SW.Dict.vec,
          ComplexEmbedding.conjugate_coe_eq, Pi.zero_apply] at h1
        have h2 := congrArg conj h1
        simpa [map_sum, hm] using h2
    apply hx
    funext p
    obtain ⟨a, j0⟩ := p
    obtain ⟨w, hw⟩ := _root_.GlobalTheory.SW.Dict.exists_emb_comb (E := E) (fun j => m (a, j))
    have hsq : ∑ j, m (a, j) * m (a, j) = 0 := by
      calc ∑ j, m (a, j) * m (a, j)
          = ∑ j, (∑ σ : E →+* ℂ, σ (Module.finBasis ℚ E j) * w σ) * m (a, j) := by
            simp only [hw]
        _ = ∑ σ : E →+* ℂ, w σ * ∑ j, σ (Module.finBasis ℚ E j) * m (a, j) := by
            simp only [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by simp [hall]
    have hsqR : ∑ j, x (a, j) * x (a, j) = 0 := by
      have : ((∑ j, x (a, j) * x (a, j) : ℝ) : ℂ) = 0 := by
        push_cast
        exact hsq
      exact_mod_cast this
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x (a, j)))).mp hsqR
      j0 (Finset.mem_univ _)
    simpa using mul_self_eq_zero.mp h0
  obtain ⟨τ0, hτ0⟩ := hex
  have hsum : 0 < ∑ τ : Ψ, (v τ ⬝ᵥ Z τ *ᵥ fun a => conj (v τ a)).im :=
    Finset.sum_pos' (fun τ _ => hnonneg τ) ⟨τ0, Finset.mem_univ _, hpos τ0 hτ0⟩
  simp only [Complex.im_sum, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
  simpa [hvdef] using mul_pos two_pos hsum
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict
