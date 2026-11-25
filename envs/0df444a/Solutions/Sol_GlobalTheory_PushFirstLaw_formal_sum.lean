-- Prove2me | solution 1 for GlobalTheory.PushFirstLaw.formal_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:19.409355+00:00
-- url     : https://prove2.me/submissions/e41d374c-c842-4d1a-b99c-684630ecc5da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstPartialLawPushAlongTripleMap
import Theorems.Thm_GlobalTheory_SecondPartialLaw_ofMul_eq
import Theorems.Thm_GlobalTheory_SecondPartialLaw_pe_pt
import Theorems.Thm_GlobalTheory_SecondPartialLaw_prod_cube2_swap
import Theorems.Thm_GlobalTheory_SecondPartialLaw_prod_cube3
import Theorems.Thm_GlobalTheory_SecondPartialLaw_pt_X
import Theorems.Thm_GlobalTheory_SecondPartialLaw_pt_law
import Theorems.Thm_GlobalTheory_SecondPartialLaw_pt_sub
import Theorems.Thm_GlobalTheory_SecondPartialLaw_th_pt


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.PushFirstLaw
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
open GlobalTheory.SecondPartialLaw
namespace GlobalTheory.PushFirstLaw
theorem _root_.solution {X0 : Scheme.{0}} {t : SAB H X0} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ}
    {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {κ : Type} [Fintype κ]
    {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uv : κ → Fin d → S} (hch : IsChartG t x0 d F act tg uv x) (m : ℕ)
    {U : Type} [CommGroup U] (h : ((jOG x0 d m 3).left ⟶ t.G.left) → U)
    (P : (Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) → U)
    (hP : ∀ φ, P φ = ∏ k, h ((Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] k) ^ cε 2 k) :
    ∏ k : thK.{0}, h ((lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left ≫
        thφ t.G (x3 t.G) k) ^ thε k =
      P ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] *
        ((P ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])⁻¹ *
          (P ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])⁻¹) := by
  have hP' : ∀ (φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (a b : jOG x0 d m 3 ⟶ t.G),
      Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 0 p.2)) ≫ x m = a →
      Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 1 p.2)) ≫ x m = b →
      P φ = h (1 : jOG x0 d m 3 ⟶ t.G).left * (h a.left)⁻¹ * (h b.left)⁻¹ * h (b * a).left := by
    rintro φ _ _ rfl rfl
    rw [← pt_sub m φ 0, ← pt_sub m φ 1]
    have e1 := Finset.prod_congr (s₁ := Finset.univ) rfl fun (k : ULift.{0} (Finset (Fin 2))) _ =>
      congrArg (fun q => h q ^ cε 2 k) (pe_pt (t := t) (x := x) m (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) k)
    have e2 := prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)
      ![Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) ≫ jptG t x0 d x m (0 : Fin 2),
        Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) ≫ jptG t x0 d x m (1 : Fin 2)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one] at e2
    exact (hP φ).trans (e1.trans e2)
  rw [hP' ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] _ _
      (pt_law hch m ![0, 1]) (pt_X m 2),
    hP' ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] _ _ (pt_X m 0) (pt_X m 2),
    hP' ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] _ _ (pt_X m 1) (pt_X m 2)]
  refine (Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ thε k) (th_pt _ _ _ k)).trans
    ((prod_cube3 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left) _).trans ?_)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, _root_.mul_one]
  generalize jptG t x0 d x m (0 : Fin 3) = a
  generalize jptG t x0 d x m (1 : Fin 3) = b
  generalize jptG t x0 d x m (2 : Fin 3) = c
  rw [_root_.mul_comm c (a * b), _root_.mul_comm c a, _root_.mul_comm c b, _root_.mul_assoc a b c]
  apply ofMul_eq
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.PushFirstLaw
