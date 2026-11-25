-- Prove2me | solution 1 for GlobalTheory.const_of_finite_family_spAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:03.896485+00:00
-- url     : https://prove2.me/submissions/b3ec7d92-8b9a-486f-a678-7aa60249957e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ProdCompEqOfFiniteFamily
import Theorems.Thm_GlobalTheory_prod_comp_eq_of_finite_family
import Theorems.Thm_GlobalTheory_differentiableOn_finite_prod
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_GlobalTheory_KeyPow_ClauseH_mono
import Theorems.Thm_GlobalTheory_KeyPow_KeyRule_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    Key.PhHoloStatement → ∀ (g : ℕ) (I : Type) [Finite I] (F : I → Matrix (Fin g) (Fin g) ℂ → ℂ), 2 ≤ g → (∀ i, Key.IsHoloSiegel g (F i)) → (∀ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, ∀ i, ∃ j, ∀ τ ∈ ReciprocityTheory.PTheta.SiegelH (Fin g), F i τ = F j (Key.Chi.spAct sp τ)) → ∀ i, ∃ c, ∀ τ ∈ ReciprocityTheory.PTheta.SiegelH (Fin g), F i τ = c := by
  intro hPh g I _ F hg hF h i
  classical
  have : Fintype I := Fintype.ofFinite I
  let S := ReciprocityTheory.PTheta.SiegelH (Fin g)
  have hmem : ∀ τ ∈ S, τ.IsSymm ∧ (τ.map Complex.im).PosDef := fun τ hτ => hτ
  let G : I → (S → ℂ) := fun j τ => F j τ
  let A : Finset (S → ℂ) := Finset.univ.image G
  have hGA : ∀ j, G j ∈ A := fun j => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hA : ∀ f ∈ A, ∃ j, G j = f := fun f hf => by simpa [A] using hf
  have : Nonempty I := ⟨i⟩
  choose! rep hrep using hA
  have heval : ∀ f ∈ A, ∀ τ (hτ : τ ∈ S), F (rep f) τ = f ⟨τ, hτ⟩ :=
    fun f hf τ hτ => congrFun (hrep f hf) ⟨τ, hτ⟩
  have hsym : ∀ τ ∈ S, Key.phSym τ = τ := by
    intro τ hτ
    have ht : Matrix.transpose τ = τ := (hmem τ hτ).1.eq
    simp only [Key.phSym, ht]
    ext p q
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hholo : ∀ w : ℂ, Key.IsHoloSiegel g (fun τ => ∏ f ∈ A, (w - F (rep f) τ)) := by
    intro w
    exact differentiableOn_finite_prod A
      (f := fun f x => w - F (rep f) (Key.phSym (Matrix.of x)))
      (fun f _ => (differentiableOn_const w).sub (hF (rep f)))
  have hinv : ∀ w : ℂ, Key.IsSpInvariant g (fun τ => ∏ f ∈ A, (w - F (rep f) τ)) := by
    intro w gm hgm τ hτ
    choose J hJ using h gm hgm
    let act : S → S := fun σ => ⟨Key.Chi.spAct gm σ, Key.Chi.spAct_mem hgm σ.2⟩
    have hfam : ∀ f ∈ A, ∃ f' ∈ A, f = f' ∘ act := by
      intro f hf
      refine ⟨G (J (rep f)), hGA _, ?_⟩
      funext σ
      exact (congrFun (hrep f hf) σ).symm.trans (hJ (rep f) σ.1 σ.2)
    have hstep := prod_comp_eq_of_finite_family A act hfam w ⟨τ, hτ⟩
    have hact : Key.phAct gm τ = Key.Chi.spAct gm τ := rfl
    show ∏ f ∈ A, (w - F (rep f) (Key.phAct gm τ)) = ∏ f ∈ A, (w - F (rep f) τ)
    calc ∏ f ∈ A, (w - F (rep f) (Key.phAct gm τ)) = ∏ f ∈ A, (w - f (act ⟨τ, hτ⟩)) :=
          Finset.prod_congr rfl (fun f hf => by rw [hact, heval f hf _ (Key.Chi.spAct_mem hgm hτ)])
      _ = ∏ f ∈ A, (w - f ⟨τ, hτ⟩) := hstep
      _ = ∏ f ∈ A, (w - F (rep f) τ) :=
          Finset.prod_congr rfl (fun f hf => by rw [heval f hf τ hτ])
  by_cases hne : S.Nonempty
  swap
  · exact ⟨0, fun τ hτ => (hne ⟨τ, hτ⟩).elim⟩
  obtain ⟨τ0, hτ0⟩ := hne
  refine ⟨F i τ0, fun τ hτ => ?_⟩
  have hval : ∀ τ ∈ S, F i τ ∈ ((A.image (fun f => F (rep f) τ0) : Finset ℂ) : Set ℂ) := by
    intro τ hτ
    obtain ⟨c, hc⟩ := hPh g hg _ (hholo (F i τ)) (hinv (F i τ))
    have h0 : ∏ f ∈ A, (F i τ - F (rep f) τ) = 0 := by
      apply Finset.prod_eq_zero (hGA i)
      rw [heval _ (hGA i) τ hτ]
      exact sub_self _
    have h1 : ∏ f ∈ A, (F i τ - F (rep f) τ0) = 0 := (hc τ0 hτ0).trans ((hc τ hτ).symm.trans h0)
    obtain ⟨f, hf, hz⟩ := Finset.prod_eq_zero_iff.1 h1
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨f, hf, (sub_eq_zero.1 hz).symm⟩)
  have hcont : ContinuousOn (F i) S := by
    have hc0 := (hF i).continuousOn
    refine (hc0.mono (fun σ hσ => ?_)).congr (fun σ hσ => ?_)
    · show Key.phSym σ ∈ S
      rw [hsym σ hσ]
      exact hσ
    · show F i σ = F i (Key.phSym σ)
      rw [hsym σ hσ]
  have hconv : Convex ℝ S := by
    intro x hx y hy s t hs ht hst
    obtain ⟨hx1, hx2⟩ := hmem x hx
    obtain ⟨hy1, hy2⟩ := hmem y hy
    change Matrix.IsSymm (s • x + t • y) ∧ ((s • x + t • y).map Complex.im).PosDef
    refine ⟨(hx1.smul s).add (hy1.smul t), ?_⟩
    have hm : (s • x + t • y).map Complex.im = s • x.map Complex.im + t • y.map Complex.im := by
      ext p q
      simp
    rw [hm]
    rcases hs.lt_or_eq with hs' | hs'
    · exact (hx2.smul hs').add_posSemidef (hy2.posSemidef.smul ht)
    · subst hs'
      rw [zero_add] at hst
      subst hst
      simpa using hy2
  exact hconv.isPreconnected.constant_of_mapsTo DiscreteTopology.isDiscrete hcont
    (fun σ hσ => hval σ hσ) hτ hτ0
end GlobalTheory
