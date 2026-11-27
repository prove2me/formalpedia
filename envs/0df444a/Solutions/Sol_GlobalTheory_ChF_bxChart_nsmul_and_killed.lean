-- Prove2me | solution 1 for GlobalTheory.ChF.bxChart_nsmul_and_killed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:35:21.272512+00:00
-- url     : https://prove2.me/submissions/46ec6ea3-b8f8-426a-a1a8-cd9523334d65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AbelianFunctorNilChartNsmulAndKilledByPPow
import Theorems.Thm_GlobalTheory_ChF_nv_calculus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
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
section
variable {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {d : ℕ} (F : FGLaw R d)
private theorem kill_cc : ∀ (N : ℕ) (j : Fin d), MvPowerSeries.constantCoeff (mulF F.F N j) = 0
  | 0, j => by simp [mulF]
  | N + 1, j => by
    have h : ∀ q : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![mulF F.F N, pt R d 0] : Fin 2 → Pt R 1 d) q.1 q.2) = 0 := by
      rintro ⟨x, l⟩
      fin_cases x
      · exact kill_cc N l
      · simp [pt]
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero h) h (F.const j)
private theorem kill_X {n : ℕ} (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (i : Fin n) (j : Fin d) :
    nv s (pt R d i j) a = a i j := by
  obtain ⟨ψ, h1, -, h3⟩ := (nv_calculus R S s n d a ha).1
  exact (h1 _).symm.trans (h3 (i, j))
private theorem kill_zero {n : ℕ} (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) :
    nv s (0 : PS R n d) a = 0 := by
  obtain ⟨ψ, h1, -, -⟩ := (nv_calculus R S s n d a ha).1
  exact (h1 _).symm.trans (map_zero ψ)
private theorem kill_one {a : Fin d → S} (ha : ∀ i, IsNilpotent (a i)) :
    ∀ i j, IsNilpotent ((![a] : Fin 1 → Fin d → S) i j) := fun i j => by
  fin_cases i; exact ha j
private theorem kill_two {a b : Fin d → S} (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) :
    ∀ i j, IsNilpotent ((![a, b] : Fin 2 → Fin d → S) i j) := fun i j => by
  fin_cases i
  · exact ha j
  · exact hb j
private theorem kill_add {n : ℕ} (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (x y : Pt R n d)
    (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0)
    (f : PS R 2 d) : nv s (ev ![x, y] f) a = nv s f ![fun l => nv s (x l) a, fun l => nv s (y l) a] := by
  have := (nv_calculus R S s n d a ha).2.2.1 2 d ![x, y] f (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j)
  refine this.trans ?_
  congr 1
  funext i
  fin_cases i <;> rfl
private theorem kill_succ {a : Fin d → S} (ha : ∀ i, IsNilpotent (a i)) (N : ℕ) (j : Fin d) :
    nv s (mulF F.F (N + 1) j) ![a] = nv s (F.F j) ![fun l => nv s (mulF F.F N l) ![a], a] := by
  refine (kill_add s ![a] (kill_one ha) _ _ (kill_cc F N) (fun l => by simp [pt]) (F.F j)).trans ?_
  congr 3
  funext l
  exact kill_X s ![a] (kill_one ha) 0 l
private theorem kill_unitL {c : Fin d → S} (hc : ∀ i, IsNilpotent (c i)) (j : Fin d) :
    nv s (F.F j) ![0, c] = c j := by
  have h := kill_add s ![c] (kill_one hc) 0 (pt R d 0) (fun l => by simp) (fun l => by simp [pt]) (F.F j)
  rw [F.unit j] at h
  have h1 : (fun l => nv s ((0 : Pt R 1 d) l) ![c]) = 0 := funext fun l => kill_zero s _ (kill_one hc)
  have h2 : (fun l => nv s (pt R d (0 : Fin 1) l) ![c]) = c := funext fun l => kill_X s _ (kill_one hc) 0 l
  rw [h1, h2] at h
  exact h.symm.trans (kill_X s _ (kill_one hc) 0 j)
private theorem kill_unitR {b : Fin d → S} (hb : ∀ i, IsNilpotent (b i)) (j : Fin d) :
    nv s (F.F j) ![b, 0] = b j := by
  have h0 := kill_two hb (fun _ => IsNilpotent.zero : ∀ i, IsNilpotent ((0 : Fin d → S) i))
  have h := kill_add s ![b, 0] h0 (pt R d 1) (pt R d 0) (fun l => by simp [pt]) (fun l => by simp [pt]) (F.F j)
  rw [F.comm j] at h
  have h1 : (fun l => nv s (pt R d (1 : Fin 2) l) ![b, 0]) = 0 := funext fun l => kill_X s _ h0 1 l
  have h2 : (fun l => nv s (pt R d (0 : Fin 2) l) ![b, 0]) = b := funext fun l => kill_X s _ h0 0 l
  rw [h1, h2] at h
  exact h.trans (kill_unitL s F hb j)
private theorem kill_sq (K : Ideal S) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = 0) {b c : Fin d → S}
    (hb : ∀ i, b i ∈ K) (hc : ∀ i, c i ∈ K) (j : Fin d) : nv s (F.F j) ![b, c] = b j + c j := by
  have hn : ∀ x ∈ K, IsNilpotent x := fun x hx => ⟨2, by rw [pow_two]; exact hK x hx x hx⟩
  have key : ∀ b c : Fin d → S, (∀ i, b i ∈ K) → (∀ i, c i ∈ K) → nv s (F.F j) ![b, c] =
      ∑ l, s (MvPowerSeries.coeff (Finsupp.single (0, l) 1) (F.F j)) * b l +
        ∑ l, s (MvPowerSeries.coeff (Finsupp.single (1, l) 1) (F.F j)) * c l := by
    intro b c hb hc
    have hm : ∀ i l, (![b, c] : Fin 2 → Fin d → S) i l ∈ K := fun i l => by
      fin_cases i
      · exact hb l
      · exact hc l
    rw [(nv_calculus R S s 2 d ![b, c] (fun i l => hn _ (hm i l))).2.2.2.2.2
      (fun _ _ _ _ => hK _ (hm _ _) _ (hm _ _)), F.const j, map_zero, zero_add, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    rfl
  have h1 := key b 0 hb (fun _ => K.zero_mem)
  have h2 := key 0 c (fun _ => K.zero_mem) hc
  rw [kill_unitR s F (fun i => hn _ (hb i))] at h1
  rw [kill_unitL s F (fun i => hn _ (hc i))] at h2
  rw [key b c hb hc, h1, h2]
  simp
private theorem kill_sqN (K : Ideal S) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = 0) {c : Fin d → S}
    (hc : ∀ i, c i ∈ K) (N : ℕ) : ∀ j, nv s (mulF F.F N j) ![c] = (N : S) * c j := by
  have hn : ∀ i, IsNilpotent (c i) := fun i => ⟨2, by rw [pow_two]; exact hK _ (hc i) _ (hc i)⟩
  induction N with
  | zero => intro j; exact (kill_zero s ![c] (kill_one hn)).trans (by simp)
  | succ N ih =>
    intro j
    rw [kill_succ s F hn, funext ih, kill_sq s F K hK (fun i => K.mul_mem_left _ (hc i)) hc]
    push_cast
    ring
private theorem kill_lin (K : Ideal S) {c : Fin d → S} (hn : ∀ i, IsNilpotent (c i))
    (hc : ∀ i, c i ∈ K) (N : ℕ) (j : Fin d) : nv s (mulF F.F N j) ![c] - (N : S) * c j ∈ K * K := by
  let t := Ideal.Quotient.mk (K * K)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_mul, map_natCast]
  refine ((nv_calculus R S s 1 d ![c] (kill_one hn)).2.2.2.2.1 _ t _).trans ?_
  have h : (fun i l => t ((![c] : Fin 1 → Fin d → S) i l)) = ![fun l => t (c l)] := by
    funext i; fin_cases i; rfl
  rw [h]
  refine kill_sqN (t.comp s) F (K.map t) ?_ (fun i => Ideal.mem_map_of_mem t (hc i)) N j
  intro x hx y hy
  obtain ⟨x, hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective t Ideal.Quotient.mk_surjective).1 hx
  obtain ⟨y, hy', rfl⟩ := (Ideal.mem_map_iff_of_surjective t Ideal.Quotient.mk_surjective).1 hy
  rw [← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_mul hx' hy')
private theorem kill_nil {c : Fin d → S} (hn : ∀ i, IsNilpotent (c i)) (N : ℕ) (j : Fin d) :
    IsNilpotent (nv s (mulF F.F N j) ![c]) :=
  ((nv_calculus R S s 1 d ![c] (kill_one hn)).2.1 _ (kill_cc F N j)).1
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
theorem _root_.solution : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (p : ℕ) (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), IsNilpotent (p : (R : Type)) → (∀ i, IsNilpotent (a i)) → (∀ N : ℕ, N • Y R s a = Y R s (fun j => nv s.1.toRingHom (mulF F.F N j) ![a])) ∧ ∃ n : ℕ, p ^ (n + 1) • Y R s a = 0 := by
  intro R₀ _ B O g F Y hY p R s a hp ha
  have h1 : ∀ a : Fin g → (R : Type), (∀ i, IsNilpotent (a i)) → ∀ N : ℕ,
      N • Y R s a = Y R s (fun j => nv s.1.toRingHom (mulF F.F N j) ![a]) := by
    intro a ha N
    induction N with
    | zero =>
      rw [zero_nsmul, ← hY.zero R s]
      congr 1
      funext j
      exact (kill_zero _ ![a] (kill_one ha)).symm
    | succ N ih =>
      rw [succ_nsmul, ih, hY.law R s _ _ (kill_nil _ F ha N) ha]
      congr 1
      funext j
      exact (kill_succ _ F ha N j).symm
  refine ⟨h1 a ha, ?_⟩
  let J : Ideal (R : Type) := Ideal.span (insert (p : (R : Type)) (Set.range a))
  have hpJ : (p : (R : Type)) ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  have h2 : ∀ k : ℕ, ∃ b : Fin g → (R : Type), (∀ i, IsNilpotent (b i)) ∧ (∀ i, b i ∈ J ^ (k + 1)) ∧
      p ^ k • Y R s a = Y R s b := by
    intro k
    induction k with
    | zero =>
      refine ⟨a, ha, fun i => ?_, by simp⟩
      rw [zero_add, pow_one]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
    | succ k ih =>
      obtain ⟨b, hb, hbJ, e⟩ := ih
      refine ⟨_, kill_nil _ F hb p, fun i => ?_, by rw [pow_succ', mul_smul, e, h1 b hb p]⟩
      have h3 := kill_lin s.1.toRingHom F (J ^ (k + 1)) hb hbJ p i
      rw [← pow_add] at h3
      have h4 : (p : (R : Type)) * b i ∈ J ^ (k + 1 + 1) := by
        rw [pow_succ' J (k + 1)]
        exact Ideal.mul_mem_mul hpJ (hbJ i)
      simpa using add_mem (Ideal.pow_le_pow_right (by omega : k + 1 + 1 ≤ k + 1 + (k + 1)) h3) h4
  have hfg : J.FG := Submodule.fg_span ((Set.finite_range a).insert _)
  have hle : J ≤ nilradical (R : Type) := by
    refine Ideal.span_le.2 ?_
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact hp
    · exact ha i
  obtain ⟨n, hn⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 hle
  obtain ⟨b, -, hbJ, e⟩ := h2 (n + 1)
  refine ⟨n, ?_⟩
  rw [e, ← hY.zero R s]
  congr 1
  funext i
  have := Ideal.pow_le_pow_right (by omega : n ≤ n + 1 + 1) (hbJ i)
  rw [hn] at this
  simpa using this
end GlobalTheory.ChF
