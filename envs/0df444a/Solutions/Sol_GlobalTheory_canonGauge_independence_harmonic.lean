-- Prove2me | solution 1 for GlobalTheory.canonGauge_independence_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:08:51.888058+00:00
-- url     : https://prove2.me/submissions/1cd75f2e-c2b6-4587-9d91-117590bd73c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeSubIsBiadd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceHarmonic
import Theorems.Thm_GlobalTheory_bilinPart_sub_eigen_eq_zero
import Theorems.Thm_GlobalTheory_canonGauge_independence_all
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_harmSecond_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B a).mulVec (u l) = σ l.1 a • u l) → ∀ (n : ℕ) (Q : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k), (∀ τ, isX τ → ∀ (i : Fin (r τ)) (i' : Fin (r (cc τ))), ∑ b : Fin n, MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b) (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) Q) = 0) → ∀ (w0 : O) (mm : ℕ) (f : Fin n → PS k 1 d), ∑ mo ∈ Q.support, Q.coeff mo * ∏ b, B.nabVal k h w0 mm (f b) u (MvPolynomial.monomial (colM mo b) 1) = ∑ mo ∈ Q.support, Q.coeff mo * ∏ b, B.nabVal k h' w0 mm (f b) u (MvPolynomial.monomial (colM mo b) 1) := by
  intro R _ d O _ _ _ _ _ k _ _ _ B h h' hh hh' T _ r cc isX σ hcc hX hσ hsep u hu n Q hQ w0 mm f
  have key : ∀ l l' : (Σ τ : T, Fin (r τ)), l'.1 ≠ cc l.1 →
      dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) = 0 := by
    intro l l' hne
    have hne' : l.1 ≠ cc l'.1 := fun e => hne (by rw [e, hcc])
    obtain ⟨a, ha⟩ := hsep _ _ hne'
    rw [hσ] at ha
    rw [hu l' w0, Matrix.mulVec_smul, dotProduct_smul,
      bilinPart_sub_eigen_eq_zero B h h' hh hh' (u l) (u l') a _ _ (hu l a) (hu l' (star a)) ha, smul_zero]
  refine canonGauge_independence_all.2.2.1 R d O k B h h' hh hh' w0 mm n _ u Q ?_ f
  refine harmSecond_holds k T r cc isX hcc hX n (fun l l' =>
    dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) +
      dotProduct (u l') ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l)))) ?_ Q hQ
  intro l l' hne
  have hne' : l.1 ≠ cc l'.1 := fun e => hne (by rw [e, hcc])
  rw [key l l' hne, key l' l hne', add_zero]
end GlobalTheory
