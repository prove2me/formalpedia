-- Prove2me | solution 1 for GlobalTheory.ChF.exists_series_of_natural
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:51.143973+00:00
-- url     : https://prove2.me/submissions/041534ac-1eb7-4dd6-a0e5-ed800cedf680

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemSupSpanXPowIffAndIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPowerSeriesOfNaturalNilpotentPoints
import Theorems.Thm_GlobalTheory_ChF_mem_sup_span_X_pow_iff_and_isAdicComplete
import Theorems.Thm_GlobalTheory_ChF_nv_calculus
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add
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
section
variable {R : Type} [CommRing R] (I : Ideal R) (n d : ℕ)
variable {n d}
variable {I}
private theorem Lev.mono {k k' : ℕ} (h : k ≤ k') {S : Type} [CommRing S] [Algebra R S]
    {a : Fin n → Fin d → S} (ha : Lev I k S a) : Lev I k' S a :=
  ⟨fun t ht => ha.1 t (Ideal.pow_le_pow_right (by omega) ht),
    le_bot_iff.1 ((Ideal.pow_le_pow_right (by omega)).trans ha.2.le)⟩
private theorem Lev.nil {k : ℕ} {S : Type} [CommRing S] [Algebra R S]
    {a : Fin n → Fin d → S} (ha : Lev I k S a) (i : Fin n) (j : Fin d) : IsNilpotent (a i j) := by
  refine ⟨k + 1, ?_⟩
  rw [← Ideal.mem_bot, ← ha.2]
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self (f := fun q : Fin n × Fin d => a q.1 q.2) (i, j))) _
private theorem exists_lev {S : Type} [CommRing S] [Algebra R S] {a : Fin n → Fin d → S}
    (hk : ∃ k, Kills I k S) (ha : ∀ i j, IsNilpotent (a i j)) : ∃ k, Lev I k S a := by
  obtain ⟨k, hk⟩ := hk
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (I := Ideal.span (Set.range fun q : Fin n × Fin d => a q.1 q.2)) (J := ⊥)
    (Ideal.span_le.2 (by rintro _ ⟨q, rfl⟩; exact ha q.1 q.2))
    (Submodule.fg_span (Set.finite_range _))
  exact ⟨k + m, fun t ht => hk t (Ideal.pow_le_pow_right (by omega) ht),
    le_bot_iff.1 ((Ideal.pow_le_pow_right (by omega)).trans hm)⟩
private theorem exists_lift {k : ℕ} {S : Type} [CommRing S] [Algebra R S]
    {a : Fin n → Fin d → S} (ha : Lev I k S a) :
    ∃ φ : MainNotions I n d k →ₐ[R] S, ∀ i j, φ (xK I n d k i j) = a i j := by
  let φ₀ : Geo.Tor.JetR R (Fin n × Fin d) k →ₐ[R] S :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun q : Fin n × Fin d => a q.1 q.2)
      (aeval_kill k _ _ (fun q => Ideal.subset_span (Set.mem_range_self q)) ha.2)
  refine ⟨Ideal.Quotient.liftₐ _ φ₀ fun y hy => ?_, fun i j => ?_⟩
  · have : (I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) k)) ≤
        RingHom.ker φ₀.toRingHom := by
      refine Ideal.map_le_iff_le_comap.2 fun t ht => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact (φ₀.commutes t).trans (ha.1 t ht)
    exact this hy
  · exact MvPolynomial.aeval_X (fun q : Fin n × Fin d => a q.1 q.2) (i, j)
private theorem lev_xK (k : ℕ) : Lev I k (MainNotions I n d k) (xK I n d k) := by
  refine ⟨fun t ht => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ht), ?_⟩
  have h := congrArg (Ideal.map (Ideal.Quotient.mk
    ((I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) k)))))
    (jet_aug_pow (T := R) (Fin n × Fin d) k)
  rw [Ideal.map_pow _ (Ideal.map _ (Ideal.span _)), Ideal.map_bot, Ideal.map_span, Ideal.map_span, ← Set.range_comp,
    ← Set.range_comp] at h
  exact h
private theorem hom_coe {S : Type} [CommRing S] [Algebra R S] (ψ : PS R n d →+* S)
    (hC : ∀ c, ψ (MvPowerSeries.C c) = algebraMap R S c) (p : MvPolynomial (Fin n × Fin d) R) :
    ψ (p : MvPowerSeries (Fin n × Fin d) R) =
      MvPolynomial.aeval (fun q => ψ (MvPowerSeries.X q)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.coe_C, MvPolynomial.aeval_C]; exact hC c
  | add p q hp hq => rw [MvPolynomial.coe_add, map_add, map_add, hp, hq]
  | mul_X p q hp => rw [MvPolynomial.coe_mul, map_mul, map_mul, hp, MvPolynomial.coe_X, MvPolynomial.aeval_X]
private theorem hom_kill {k : ℕ} {S : Type} [CommRing S] [Algebra R S]
    {a : Fin n → Fin d → S} (ha : Lev I k S a) (ψ : PS R n d →+* S)
    (hC : ∀ c, ψ (MvPowerSeries.C c) = algebraMap R S c)
    (hX : ∀ q : Fin n × Fin d, ψ (MvPowerSeries.X q) = a q.1 q.2) (g : PS R n d)
    (hg : g ∈ JJ I n d ^ (k + 1 + (k + 1))) : ψ g = 0 := by
  have h1 : JJ I n d ^ (k + 1 + (k + 1)) ≤ RingHom.ker ψ := by
    refine Ideal.sup_pow_add_le_pow_sup_pow.trans (sup_le ?_ ?_)
    · rw [← Ideal.map_pow]
      refine Ideal.map_le_iff_le_comap.2 fun t ht => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact (hC t).trans (ha.1 t ht)
    · rw [RingHom.ker, ← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span, ← Set.range_comp,
        ← ha.2]
      exact le_of_eq (by congr 3; exact funext hX)
  exact h1 hg
private theorem exists_poly (N : ℕ) (g : PS R n d) :
    ∃ p : MvPolynomial (Fin n × Fin d) R, g - (p : MvPowerSeries (Fin n × Fin d) R) ∈ JJ I n d ^ N := by
  refine ⟨MvPowerSeries.truncTotal N g,
    ((mem_sup_span_X_pow_iff_and_isAdicComplete R I (Fin n × Fin d)).1 N _).2 fun e => ?_⟩
  by_cases he : e.degree < N
  · rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ he, sub_self]
    exact Ideal.zero_mem _
  · rw [show N - e.degree = 0 by omega]
    simp
private theorem nv_lift {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
    (φ : S →ₐ[R] S') {a : Fin n → Fin d → S} (ha : ∀ i j, IsNilpotent (a i j)) (g : PS R n d) :
    φ (nv (algebraMap R S) g a) = nv (algebraMap R S') g (fun i j => φ (a i j)) := by
  have h := (nv_calculus R S (algebraMap R S) n d a ha).2.2.2.2.1 S' φ.toRingHom g
  rw [show φ.toRingHom.comp (algebraMap R S) = algebraMap R S' from RingHom.ext φ.commutes] at h
  exact h
private theorem mem_of_nv_eq (k : ℕ) (g g' : PS R n d)
    (h : nv (algebraMap R _) g (xK I n d k) = nv (algebraMap R _) g' (xK I n d k)) :
    g - g' ∈ JJ I n d ^ (k + 1) := by
  let π : PS R n d →+* PS R n d ⧸ JJ I n d ^ (k + 1) := Ideal.Quotient.mk _
  have hπC : ∀ c, π (MvPowerSeries.C c) = algebraMap R _ c := fun c => rfl
  have hl : Lev I k (PS R n d ⧸ JJ I n d ^ (k + 1)) (fun i j => π (MvPowerSeries.X (i, j))) := by
    refine ⟨fun t ht => ?_, ?_⟩
    · rw [← hπC]
      refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_right_mono le_sup_left _ ?_)
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ht
    · rw [← le_bot_iff, ← Ideal.map_quotient_self (JJ I n d ^ (k + 1)), Ideal.map_pow]
      refine Ideal.pow_right_mono (Ideal.span_le.2 ?_) _
      rintro _ ⟨q, rfl⟩
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩))
  obtain ⟨φ, hφ⟩ := exists_lift hl
  obtain ⟨ψ, hψ, hC, hX⟩ := (nv_calculus R _ (algebraMap R _) n d _ hl.nil).1
  have hψπ : ∀ u, ψ u = π u := fun u => by
    obtain ⟨p, hp⟩ := exists_poly (I := I) (k + 1 + (k + 1)) u
    have h1 := hom_kill hl ψ hC hX _ hp
    have h2 := hom_kill hl π hπC (fun _ => rfl) _ hp
    rw [map_sub, sub_eq_zero] at h1 h2
    rw [h1, h2, hom_coe ψ hC, hom_coe π hπC]
    simp only [hX]
  have h3 := congrArg φ h
  rw [nv_lift φ (lev_xK k).nil, nv_lift φ (lev_xK k).nil] at h3
  simp only [hφ] at h3
  rw [← hψ, ← hψ, hψπ, hψπ] at h3
  exact Ideal.Quotient.eq.1 h3
private theorem nv_surj (k : ℕ) (y : MainNotions I n d k) :
    ∃ g : PS R n d, nv (algebraMap R _) g (xK I n d k) = y := by
  obtain ⟨ψ, hψ, hC, hX⟩ := (nv_calculus R _ (algebraMap R _) n d _ (lev_xK (I := I) k).nil).1
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨(p : MvPowerSeries (Fin n × Fin d) R), ?_⟩
  rw [← hψ, hom_coe ψ hC]
  have : MvPolynomial.aeval (fun q => ψ (MvPowerSeries.X q)) =
      (Ideal.Quotient.mkₐ R _).comp (Ideal.Quotient.mkₐ R _) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    rw [MvPolynomial.aeval_X, hX]
    rfl
  rw [this]
  rfl
private theorem const_add_nil (k : ℕ) (y : MainNotions I n d k) :
    ∃ r : R, IsNilpotent (y - algebraMap R _ r) := by
  obtain ⟨g, rfl⟩ := nv_surj k y
  obtain ⟨⟨ψ, hψ, hC, -⟩, h0, -⟩ := nv_calculus R _ (algebraMap R _) n d _ (lev_xK (I := I) k).nil
  refine ⟨MvPowerSeries.constantCoeff g, ?_⟩
  have := (h0 (g - MvPowerSeries.C (MvPowerSeries.constantCoeff g)) (by simp)).1
  rwa [← hψ, map_sub, hC, hψ] at this
end
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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (n d : ℕ) (L : ∀ (S : Type) [CommRing S] [Algebra R S], Prop), (∀ (k m : ℕ), L (Geo.Tor.JetR R (Fin n × Fin d) m ⧸ (I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) m)))) → ∀ (c : ∀ (S : Type) [CommRing S] [Algebra R S], (Fin n → Fin d → S) → S), (∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (a : Fin n → Fin d → S), L S → L S' → (∀ y : S, ∃ r : R, IsNilpotent (y - algebraMap R S r)) → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → φ (c S a) = c S' (fun i j => φ (a i j))) → ∃ f : PS R n d, ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S), L S → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → c S a = nv (algebraMap R S) f a := by
  intro R _ I hI n d L hL c hc
  choose g hg using fun k => nv_surj k (c (MainNotions I n d k) (xK I n d k))
  have key : ∀ (k : ℕ) (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S), L S →
      Lev I k S a → c S a = nv (algebraMap R S) (g k) a := by
    intro k S _ _ a hS ha
    obtain ⟨φ, hφ⟩ := exists_lift ha
    have h1 := hc _ S φ (xK I n d k) (hL k k) hS (const_add_nil k) ⟨k, (lev_xK k).1⟩ (lev_xK k).nil
    rw [← hg, nv_lift φ (lev_xK k).nil] at h1
    simp only [hφ] at h1
    exact h1.symm
  have hcomp : IsAdicComplete (JJ I n d) (PS R n d) :=
    (mem_sup_span_X_pow_iff_and_isAdicComplete R I (Fin n × Fin d)).2 hI
  obtain ⟨f, hf⟩ := hcomp.toIsPrecomplete.prec (f := g) fun {k k'} h => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    refine Ideal.pow_le_pow_right (Nat.le_succ k) (mem_of_nv_eq k _ _ ?_)
    rw [← key k _ _ (hL k k) (lev_xK k), ← key k' _ _ (hL k k) ((lev_xK k).mono h)]
  refine ⟨f, fun S _ _ a hS hk ha => ?_⟩
  obtain ⟨k, hk⟩ := exists_lev hk ha
  obtain ⟨ψ, hψ, hC, hX⟩ := (nv_calculus R _ (algebraMap R S) n d _ ha).1
  have h1 := hf (k + 1 + (k + 1))
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hom_kill hk ψ hC hX _ h1
  rw [map_sub, sub_eq_zero, hψ, hψ] at h2
  rw [key (k + 1 + (k + 1)) S a hS (hk.mono (by omega)), h2]
end GlobalTheory.ChF
