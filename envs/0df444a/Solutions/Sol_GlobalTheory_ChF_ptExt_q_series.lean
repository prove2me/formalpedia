-- Prove2me | solution 1 for GlobalTheory.ChF.ptExt_q_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:29:01.043288+00:00
-- url     : https://prove2.me/submissions/a351fc8c-f978-487e-ba51-20f255395250

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSeriesEqOfEvalAtNilpotentPointsEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPowerSeriesOfNaturalNilpotentPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ToricPointExtensionAbelianPartFormalGroupHom
import Theorems.Thm_GlobalTheory_ChF_nv_calculus
import Theorems.Thm_GlobalTheory_T_exists_powerSeries_of_natural_nilpotentPoints
import Theorems.Thm_GlobalTheory_T_powerSeries_eq_of_evalAtNilpotentPoints_eq
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_const
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_prod
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
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.pderivEval_X
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
private theorem kills_of_algHom {R : Type} [CommRing R] {I : Ideal R} {S S' : Type} [CommRing S] [Algebra R S]
    [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (h : ∃ k, Kills I k S) : ∃ k, Kills I k S' := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, fun t ht => by rw [← φ.commutes, hk t ht, map_zero]⟩
private theorem exists_split_thickening {R : Type} [CommRing R] {d : ℕ} (S : Type) [CommRing S] [Algebra R S]
    (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra R T) (ρ π : T →ₐ[R] S) (σ : S →ₐ[R] T) (a' : Fin d → T),
      ρ.comp σ = AlgHom.id R S ∧ IsNilpotent (RingHom.ker ρ) ∧ (∀ i, ρ (a' i) = 0) ∧ ∀ i, π (a' i) = a i := by
  let J : Ideal S := Ideal.span (Set.range a)
  have hJ : IsNilpotent J := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range a))).2 ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ha i
  let T : Subalgebra R (S × S) := AlgHom.equalizer ((Ideal.Quotient.mkₐ R J).comp (AlgHom.fst R S S))
    ((Ideal.Quotient.mkₐ R J).comp (AlgHom.snd R S S))
  let ρ : T →ₐ[R] S := (AlgHom.fst R S S).comp T.val
  let π : T →ₐ[R] S := (AlgHom.snd R S S).comp T.val
  let σ : S →ₐ[R] T := ((AlgHom.id R S).prod (AlgHom.id R S)).codRestrict T (fun _ => rfl)
  have hm : ∀ i, ((0, a i) : S × S) ∈ T := fun i => by
    show Ideal.Quotient.mk J 0 = Ideal.Quotient.mk J (a i)
    rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨i, rfl⟩
  refine ⟨T, inferInstance, inferInstance, ρ, π, σ, fun i => ⟨(0, a i), hm i⟩, rfl, ?_, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨N, hN⟩ := hJ
  have hle : RingHom.ker ρ ≤ J.comap π := fun t ht => by
    have h1 : t.1.1 = 0 := ht
    have h2 : Ideal.Quotient.mk J t.1.1 = Ideal.Quotient.mk J t.1.2 := t.2
    rw [h1, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at h2
    exact h2
  refine ⟨N + 1, le_bot_iff.1 fun t ht => ?_⟩
  have h1 : t.1.1 = 0 := (Ideal.pow_le_self (Nat.succ_ne_zero N) ht : t ∈ RingHom.ker ρ)
  have h2 := Ideal.le_comap_pow π N (Ideal.pow_right_mono hle N (Ideal.pow_le_pow_right (Nat.le_succ N) ht))
  rw [hN] at h2
  have h3 : π t = 0 := by simpa using h2
  exact Subtype.ext (Prod.ext h1 h3)
private theorem exists_nilpotent_image {R : Type} [CommRing R] {I : Ideal R}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {B : Over (Spec (CommRingCat.of R))} [GrpObj B]
    {X : Type} [AddCommGroup X] (E : PtExt I G B X) {d g : ℕ} {F : Fin d → PS R 2 d} {FB : Fin g → PS R 2 g}
    {x : Fam G d} {xB : Fam B g} (hx : NilChart G F x) (hB : NilChart B FB xB)
    (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ b : Fin g → S, (∀ j, IsNilpotent (b j)) ∧ E.q S h (x S a) = xB S b := by
  obtain ⟨T, _, _, ρ, π, σ, a', hσ, ⟨N, hN⟩, h0, h1⟩ := exists_split_thickening (R := R) S a ha
  have hT := kills_of_algHom σ h
  have hnil : ∀ t : T, ρ t = 0 → IsNilpotent t := fun t ht => ⟨N, by
    have := Ideal.pow_mem_pow (show t ∈ RingHom.ker ρ from ht) N
    rw [hN] at this
    simpa using this⟩
  have ha' : ∀ i, IsNilpotent (a' i) := fun i => hnil _ (h0 i)
  obtain ⟨b, hb, hz⟩ := hB.surj T S ρ σ hσ ⟨N, hN⟩ (E.q T hT (x T a')) (by
    rw [← E.q_nat T S ρ hT h, hx.nat T S ρ a' ha', show (fun i => ρ (a' i)) = 0 from funext h0, hx.zero,
      map_one])
  have hb' : ∀ j, IsNilpotent (b j) := fun j => hnil _ (hb j)
  refine ⟨fun j => π (b j), fun j => (hb' j).map π, ?_⟩
  rw [← hB.nat T S π b hb', ← hz, ← E.q_nat T S π hT h, hx.nat T S π a' ha', show (fun i => π (a' i)) = a from funext h1]
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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∃ Q : Fin g → PS R 1 d, IsHomF F.F FB.F Q ∧ (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) := by
  intro R _ I hI G _ _ B _ _ X _ E d g F FB x xB hx hB
  classical
  let c : ∀ (S : Type) [CommRing S] [Algebra R S], (Fin d → S) → Fin g → S := fun S _ _ a =>
    if h : (∃ k, Kills I k S) ∧ ∀ i, IsNilpotent (a i) then
      (exists_nilpotent_image E hx hB S h.1 a h.2).choose else 0
  have hc : ∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S),
      (∀ i, IsNilpotent (a i)) → (∀ j, IsNilpotent (c S a j)) ∧ E.q S h (x S a) = xB S (c S a) := by
    intro S _ _ h a ha
    have : c S a = (exists_nilpotent_image E hx hB S h a ha).choose := dif_pos ⟨h, ha⟩
    rw [this]
    exact (exists_nilpotent_image E hx hB S h a ha).choose_spec
  have hnat : ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S')
      (a : Fin d → S), (∃ k, Kills I k S) → (∀ i, IsNilpotent (a i)) →
      (fun j => φ (c S a j)) = c S' (fun i => φ (a i)) := by
    intro S _ _ S' _ _ φ a h ha
    have h' := kills_of_algHom φ h
    have ha' : ∀ i, IsNilpotent (φ (a i)) := fun i => (ha i).map φ
    refine hB.inj S' _ _ (fun j => ((hc S h a ha).1 j).map φ) (hc S' h' _ ha').1 ?_
    rw [← (hc S' h' _ ha').2, ← hB.nat S S' φ _ (hc S h a ha).1, ← (hc S h a ha).2, ← E.q_nat S S' φ h h',
      hx.nat S S' φ a ha]
  choose Q hQ using fun j : Fin g => GlobalTheory.T.exists_powerSeries_of_natural_nilpotentPoints R I hI 1 d (fun _ _ _ => True) (fun _ _ => trivial)
    (fun S _ _ a => c S (a 0) j)
    (fun S _ _ S' _ _ φ a _ _ _ h ha => congrFun (hnat S S' φ (a 0) h (ha 0)) j)
  have hQ' : ∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S),
      (∀ i, IsNilpotent (a i)) → (fun j => nv (algebraMap R S) (Q j) ![a]) = c S a := by
    intro S _ _ h a ha
    funext j
    exact (hQ j S ![a] trivial h (fun i l => by fin_cases i; exact ha l)).symm
  have hconst : ∀ j, MvPowerSeries.constantCoeff (Q j) = 0 := by
    intro j
    refine IsHausdorff.haus (I := I) inferInstance _ fun k => ?_
    have hk : ∃ m, Kills I m (R ⧸ I ^ (k + 1)) := ⟨k, fun t ht => Ideal.Quotient.eq_zero_iff_mem.2 ht⟩
    have h0 : ∀ i : Fin d, IsNilpotent ((0 : Fin d → R ⧸ I ^ (k + 1)) i) := fun _ => IsNilpotent.zero
    have h1 : c (R ⧸ I ^ (k + 1)) 0 = 0 :=
      hB.inj _ _ _ (hc _ hk 0 h0).1 (fun _ => IsNilpotent.zero) (by
        rw [← (hc _ hk 0 h0).2, hx.zero, hB.zero, map_one])
    have h2 := congrFun (hQ' _ hk 0 h0) j
    have h3 := (nv_calculus R (R ⧸ I ^ (k + 1)) (algebraMap _ _) 1 d ![0]
      (fun i l => by fin_cases i; exact h0 l)).2.2.2.2.2 (fun i l i' l' => by fin_cases i; simp) (Q j)
    rw [h1] at h2
    rw [h2] at h3
    have h4 : algebraMap R (R ⧸ I ^ (k + 1)) (MvPowerSeries.constantCoeff (Q j)) = 0 := by
      simpa using h3.symm
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (Nat.le_succ k) (Ideal.Quotient.eq_zero_iff_mem.1 h4)
  refine ⟨Q, ⟨hconst, fun j => ?_⟩, fun S _ _ h a ha => by rw [hQ' S h a ha]; exact (hc S h a ha).2⟩
  refine GlobalTheory.T.powerSeries_eq_of_evalAtNilpotentPoints_eq R I inferInstance 2 d _ _ fun S _ _ k hk _ a ha => ?_
  have h : ∃ k, Kills I k S := ⟨k, hk⟩
  obtain ⟨⟨ψ, hψ, -, hX⟩, hn, hs, -⟩ := nv_calculus R S (algebraMap R S) 2 d a ha
  have hpt : ∀ i : Fin 2, ∀ l, nv (algebraMap R S) (ev (n := 2) ![pt R d i] (Q l)) a = c S (a i) l := by
    intro i l
    have e := hs 1 d ![pt R d i] (Q l) (fun i' l' => by fin_cases i'; simp [pt])
    have e2 : (fun i' l' => nv (algebraMap R S) ((![pt R d i] : Fin 1 → Fin d → PS R 2 d) i' l') a) = ![a i] := by
      funext i' l'
      fin_cases i'
      exact (hψ _).symm.trans (hX (i, l'))
    rw [e2] at e
    exact e.trans (congrFun (hQ' S h (a i) (ha i)) l)
  have hpc : ∀ i : Fin 2, ∀ l, MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d i] (Q l)) = 0 := by
    intro i l
    refine MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero ?_) ?_ (hconst l)
    all_goals
      rintro ⟨i', l'⟩
      fin_cases i'
      simp [pt]
  have ea : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
  have hFn : ∀ l, IsNilpotent (nv (algebraMap R S) (F.F l) a) := fun l => (hn _ (F.const l)).1
  have e1 := hs 1 d ![F.F] (Q j) (fun i' l' => by fin_cases i'; exact F.const l')
  have e2 : (fun i' l' => nv (algebraMap R S) ((![F.F] : Fin 1 → Fin d → PS R 2 d) i' l') a) =
      ![fun l => nv (algebraMap R S) (F.F l) a] := by
    funext i' l'
    fin_cases i'
    rfl
  rw [e2] at e1
  have e3 := hs 2 g ![fun i => ev (n := 2) ![pt R d 0] (Q i), fun i => ev (n := 2) ![pt R d 1] (Q i)] (FB.F j)
    (fun i' l' => by fin_cases i'; exacts [hpc 0 l', hpc 1 l'])
  have e4 : (fun i' l' => nv (algebraMap R S) ((![fun i => ev (n := 2) ![pt R d 0] (Q i),
      fun i => ev (n := 2) ![pt R d 1] (Q i)] : Fin 2 → Fin g → PS R 2 d) i' l') a) = ![c S (a 0), c S (a 1)] := by
    funext i' l'
    fin_cases i'
    exacts [hpt 0 l', hpt 1 l']
  rw [e4] at e3
  have hcn : ∀ i l, IsNilpotent ((![c S (a 0), c S (a 1)] : Fin 2 → Fin g → S) i l) := fun i l => by
    fin_cases i
    exacts [(hc S h _ (ha 0)).1 l, (hc S h _ (ha 1)).1 l]
  have key : c S (fun l => nv (algebraMap R S) (F.F l) a) =
      fun l => nv (algebraMap R S) (FB.F l) ![c S (a 0), c S (a 1)] := by
    refine hB.inj S _ _ (hc S h _ hFn).1
      (fun l => ((nv_calculus R S (algebraMap R S) 2 g _ hcn).2.1 _ (FB.const l)).1) ?_
    rw [← (hc S h _ hFn).2, ← hB.law S _ _ (hc S h _ (ha 0)).1 (hc S h _ (ha 1)).1, ← (hc S h _ (ha 0)).2,
      ← (hc S h _ (ha 1)).2, ← map_mul, hx.law S _ _ (ha 0) (ha 1), ← ea]
  rw [e3]
  exact e1.trans ((congrFun (hQ' S h _ hFn) j).trans (congrFun key j))
end GlobalTheory.ChF
