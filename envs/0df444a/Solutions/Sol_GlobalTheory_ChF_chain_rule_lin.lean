-- Prove2me | solution 1 for GlobalTheory.ChF.chain_rule_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:44.334377+00:00
-- url     : https://prove2.me/submissions/b611dc79-9634-4e8e-948f-8a5c159f38d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalSeriesJacobianChainRuleLinearPart
import Theorems.Thm_GlobalTheory_ChF_nv_calculus
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_const
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
private theorem hs {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (h : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) :
    MvPowerSeries.HasSubst (fun q : Fin m × Fin d => a q.1 q.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => h q.1 q.2)
private theorem sub_sub' {R : Type} [CommRing R] {m n k d e f : ℕ} (a : Fin m → Fin d → PS R n e)
    (b : Fin n → Fin e → PS R k f) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
    (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) (u : PS R m d) :
    sub b (sub a u) = sub (fun i j => sub b (a i j)) u :=
  MvPowerSeries.subst_comp_subst_apply (hs a ha) (hs b hb) u
private theorem sub_X {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (q : Fin m × Fin d) :
    sub a (MvPowerSeries.X q) = a q.1 q.2 :=
  MvPowerSeries.subst_X (hs a ha) q
private theorem sub_mul' {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (u v : PS R m d) :
    sub a (u * v) = sub a u * sub a v :=
  MvPowerSeries.subst_mul (hs a ha) u v
private theorem const_sub {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (u : PS R m d) :
    MvPowerSeries.constantCoeff (sub a u) = MvPowerSeries.constantCoeff u := by
  obtain ⟨-, -, h3, -, -, h6⟩ := nv_calculus R R (RingHom.id R) n e 0 (fun _ _ => IsNilpotent.zero)
  obtain ⟨-, -, -, -, -, h6'⟩ := nv_calculus R R (RingHom.id R) m d 0 (fun _ _ => IsNilpotent.zero)
  have h6 := h6 (by simp)
  have h6' := h6' (by simp)
  have h := h3 m d a u ha
  have e0 : (fun i j => nv (RingHom.id R) (a i j) 0) = 0 := by
    funext i j
    rw [h6, ha]; simp
  rw [e0, h6, h6'] at h
  simpa using h
private theorem coeff_sub {R : Type} [CommRing R] {d e : ℕ} (φ : Fin e → PS R 1 d)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (u : PS R 1 e) (k : Fin d) :
    dl (sub ![φ] u) k = ∑ i, lin φ i k * dl u i := by
  classical
  have hφ' : ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → _) i j) = 0 := by
    intro i j; fin_cases i; exact hφ j
  let s : R →+* TrivSqZeroExt R R := algebraMap R _
  let a : Fin 1 → Fin d → TrivSqZeroExt R R := fun _ j => TrivSqZeroExt.inr (if j = k then 1 else 0)
  let b : Fin 1 → Fin e → TrivSqZeroExt R R := fun _ j => TrivSqZeroExt.inr (lin φ j k)
  have hn : ∀ x : R, IsNilpotent (TrivSqZeroExt.inr x : TrivSqZeroExt R R) := fun x =>
    ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩
  obtain ⟨-, -, h3, -, -, h6⟩ := nv_calculus R _ s 1 d a (fun _ _ => hn _)
  obtain ⟨-, -, -, -, -, h6'⟩ := nv_calculus R _ s 1 e b (fun _ _ => hn _)
  have h6 := h6 (fun _ _ _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  have h6' := h6' (fun _ _ _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  have h := h3 1 e ![φ] u hφ'
  have e0 : (fun i j => nv s ((![φ] : Fin 1 → _) i j) a) = b := by
    funext i j
    fin_cases i
    rw [h6, hφ']
    ext
    · have hf : ∀ (t : Finset (Fin 1 × Fin d)) (g : Fin 1 × Fin d → TrivSqZeroExt R R),
          (∑ q ∈ t, g q).fst = ∑ q ∈ t, (g q).fst := fun t g =>
        map_sum (TrivSqZeroExt.fstHom R R R) g t
      simp [s, a, b, hf, apply_ite TrivSqZeroExt.fst]
    · simp [s, a, b, TrivSqZeroExt.snd_sum, Fintype.sum_prod_type, lin, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e0, h6, h6'] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  simpa [s, a, b, TrivSqZeroExt.snd_sum, Fintype.sum_prod_type, TrivSqZeroExt.algebraMap_eq_inl, dl,
    mul_comm] using h2
end GlobalTheory.ChF
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d e : ℕ) (φ : Fin e → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∀ u : PS R 1 e, dl (sub ![φ] u) = (lin φ)ᵀ *ᵥ dl u ∧ MvPowerSeries.constantCoeff (sub ![φ] u) = MvPowerSeries.constantCoeff u) ∧ (∀ (m : ℕ) (ψ : Fin m → PS R 1 e), lin (fun j => sub ![φ] (ψ j)) = lin ψ * lin φ) ∧ ∀ (F : FGLaw R d) (F' : FGLaw R e), IsHomF F.F F'.F φ → ∀ u, IsCh F'.F u → IsCh F.F (sub ![φ] u) := by
  intro R _ d e φ hφ
  have one : ∀ {n f g : ℕ} (x : Fin g → PS R n f), (∀ j, MvPowerSeries.constantCoeff (x j) = 0) →
      ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![x] : Fin 1 → _) i j) = 0 := by
    intro n f g x hx i j; fin_cases i; exact hx j
  have two : ∀ {n f g : ℕ} (x y : Fin g → PS R n f), (∀ j, MvPowerSeries.constantCoeff (x j) = 0) →
      (∀ j, MvPowerSeries.constantCoeff (y j) = 0) →
      ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![x, y] : Fin 2 → _) i j) = 0 := by
    intro n f g x y hx hy i j; fin_cases i
    · exact hx j
    · exact hy j
  have hφ' := one φ hφ
  refine ⟨fun u => ⟨?_, const_sub _ hφ' u⟩, fun m ψ => ?_, fun F F' hF u hu => ⟨?_, ?_⟩⟩
  · funext k
    rw [coeff_sub φ hφ u k]
    rfl
  · ext j k
    have := coeff_sub φ hφ (ψ j) k
    rw [Matrix.mul_apply]
    refine this.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _)
  · rw [const_sub _ hφ' u, hu.1]
  · have hpt : ∀ (f : ℕ) (i : Fin 2) j, MvPowerSeries.constantCoeff (pt R (n := 2) f i j) = 0 :=
      fun f i j => MvPowerSeries.constantCoeff_X _
    have hid : ∀ (f : ℕ) (G : Fin f → PS R 2 f), addOf G (pt R (n := 2) f 0) (pt R (n := 2) f 1) = G := by
      intro f G
      funext i
      have : (fun p : Fin 2 × Fin f => (![pt R (n := 2) f 0, pt R (n := 2) f 1] : Fin 2 → _) p.1 p.2)
          = MvPowerSeries.X := by
        funext ⟨p, q⟩
        fin_cases p <;> rfl
      simp only [addOf, ev]
      rw [this, MvPowerSeries.subst_self]
      rfl
    have hu2 := hu.2
    rw [hid] at hu2 ⊢
    set x : Fin e → PS R 2 d := fun i => sub ![pt R (n := 2) d 0] (φ i) with hx
    set y : Fin e → PS R 2 d := fun i => sub ![pt R (n := 2) d 1] (φ i) with hy
    have hx0 : ∀ j, MvPowerSeries.constantCoeff (x j) = 0 := fun j => by
      rw [hx]; dsimp only; rw [const_sub _ (one _ (hpt d 0)), hφ]
    have hy0 : ∀ j, MvPowerSeries.constantCoeff (y j) = 0 := fun j => by
      rw [hy]; dsimp only; rw [const_sub _ (one _ (hpt d 1)), hφ]
    have hxy := two x y hx0 hy0
    have h : sub ![x, y] (sub ![F'.F] u) =
        sub ![x, y] (sub ![pt R (n := 2) e 0] u * sub ![pt R (n := 2) e 1] u) := congrArg _ hu2
    rw [sub_mul' _ hxy, sub_sub' _ _ (one _ F'.const) hxy, sub_sub' _ _ (one _ (hpt e 0)) hxy,
      sub_sub' _ _ (one _ (hpt e 1)) hxy] at h
    change sub ![F.F] (sub ![φ] u) =
      sub ![pt R (n := 2) d 0] (sub ![φ] u) * sub ![pt R (n := 2) d 1] (sub ![φ] u)
    rw [sub_sub' _ _ hφ' (one _ F.const), sub_sub' _ _ hφ' (one _ (hpt d 0)),
      sub_sub' _ _ hφ' (one _ (hpt d 1))]
    have e1 : (fun i j => sub ![F.F] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![F'.F] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact hF.2 j
    have e2 : (fun i j => sub ![pt R (n := 2) d 0] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![pt R (n := 2) e 0] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact (sub_X _ hxy (0, j)).symm
    have e3 : (fun i j => sub ![pt R (n := 2) d 1] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![pt R (n := 2) e 1] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact (sub_X _ hxy (1, j)).symm
    rw [e1, e2, e3]
    exact h
end GlobalTheory.ChF
