-- Prove2me | solution 1 for GlobalTheory.nabValN_harmonic_gauge_independent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:20:39.606386+00:00
-- url     : https://prove2.me/submissions/3459ffb3-4e4b-475e-acf7-ac422cb9c053

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_HarmonicValueCopiesGaugeIndependent
import Theorems.Thm_GlobalTheory_HarmCopies_monomial_eq_boxSer
import Theorems.Thm_GlobalTheory_HarmCopies_exists_jet
import Theorems.Thm_GlobalTheory_HarmCopies_const_eq_zero
import Theorems.Thm_GlobalTheory_HarmCopies_col_sum_eq_zero
import Theorems.Thm_GlobalTheory_PowGerm_nabJet
import Theorems.Thm_GlobalTheory_canonGauge_independence_harmonic
import Theorems.Thm_GlobalTheory_nabValN_boxSer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory
open HarmCopies PowGerm
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B a).mulVec (u l) = σ l.1 a • u l) → ∀ (n : ℕ) (P : MvPolynomial (Letter T r n) k), P ∈ harmK r n k cc isX (fun _ => 1) → ∀ (w0 : O) (q : ℕ) (f : PS k n d), nabValN B k h w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B k h' w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P := by
  intro R _ d O _ _ _ _ _ k _ _ _ B h h' hh hh' T _ r cc isX σ hcc hX hσ hsep u hu n P hP w0 q f
  obtain ⟨Q, rfl⟩ : ∃ Q, MvPolynomial.rename (letterEquiv T r n) Q = P :=
    MvPolynomial.rename_surjective _ (letterEquiv T r n).surjective P
  obtain ⟨S, hS⟩ := exists_jet (MvPolynomial.rename (letterEquiv T r n) Q).totalDegree f
  rw [(nabJet R d O B k h w0 q n _ _ _).1 _ _ _ hS, (nabJet R d O B k h' w0 q n _ _ _).1 _ _ _ hS,
    (nabJet R d O B k h w0 q n _ _ _).2.1, (nabJet R d O B k h' w0 q n _ _ _).2.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [monomial_eq_boxSer,
    nabValN_boxSer R d O B k h w0 (const_eq_zero hh) q n _ _ _ (letterEquiv T r n) _ u _ (fun _ => rfl) (fun _ => rfl),
    nabValN_boxSer R d O B k h' w0 (const_eq_zero hh') q n _ _ _ (letterEquiv T r n) _ u _ (fun _ => rfl) (fun _ => rfl)]
  exact canonGauge_independence_harmonic R d O k B h h' hh hh' T r cc isX σ hcc hX hσ hsep u hu n Q
    (col_sum_eq_zero Q hP) w0 q _
end GlobalTheory
