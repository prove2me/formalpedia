-- Prove2me | solution 1 for GlobalTheory.series_two_points_eq_sum_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:45.53257+00:00
-- url     : https://prove2.me/submissions/f95e4cca-0f30-4275-9c94-e0bc74487156

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesEvalOfPowMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SeriesTwoPointsEqSumMul
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_mvPowerSeries_eval_of_pow_mem
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
namespace GlobalTheory
namespace SeriesTensor
private theorem mem_smul_top_iff {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ (I • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    have hle : (I • ⊤ : Submodule R M) ≤ Submodule.comap (b.coord i) I :=
      Submodule.smul_le.2 fun r hr m _ => by
        rw [Submodule.mem_comap, map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top
private theorem isAdicComplete_of_basis {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) [hI : IsAdicComplete I R] :
    IsAdicComplete I M := by
  have htop : ∀ k : ℕ, (I ^ k • ⊤ : Submodule R R) = I ^ k := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus' (I := I) _ fun n => ?_
    have := hx n
    rw [SModEq.zero, mem_smul_top_iff b] at this
    rw [SModEq.zero, htop]
    exact this i
  have hP' : IsPrecomplete I M := by
    rw [isPrecomplete_iff]
    intro F hF
    have hP := hI.toIsPrecomplete
    rw [isPrecomplete_iff] at hP
    have hc : ∀ i, ∃ L : R, ∀ k, b.repr (F k) i ≡ L [SMOD (I ^ k • ⊤ : Submodule R R)] := by
      intro i
      refine hP (fun k => b.repr (F k) i) fun {m n} hmn => ?_
      have := hF hmn
      rw [SModEq.sub_mem, mem_smul_top_iff b] at this
      rw [SModEq.sub_mem, htop]
      simpa using this i
    choose L hL using hc
    refine ⟨∑ i, L i • b i, fun k => ?_⟩
    rw [SModEq.sub_mem, mem_smul_top_iff b]
    intro i
    have := hL i k
    rw [SModEq.sub_mem, htop] at this
    have hr : b.repr (∑ j, L j • b j) i = L i := by
      have h := congrFun (b.equivFun.apply_symm_apply L) i
      rwa [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply] at h
    rw [map_sub, Finsupp.sub_apply, hr]
    exact this
  exact { toIsHausdorff := hH, toIsPrecomplete := hP' }
private theorem exists_pow_mem {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) {a c : O} (ha : algebraMap O C a ≠ 0) (hc : ¬ IsUnit c) :
    ∃ n : ℕ, c ^ n ∈ Ideal.span {a} := by
  have h1 : v (algebraMap O C c) < 1 :=
    lt_of_le_of_ne (hv.map_le_one c) fun h => hc (hv.isUnit_iff_valuation_eq_one.2 h)
  have h0 : 0 < v (algebraMap O C a) := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 ha)
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one h0 h1
  refine ⟨n, Ideal.mem_span_singleton.2 (hv.dvd_of_le ?_)⟩
  rw [map_pow, map_pow]
  exact hn.le
private theorem exists_pow_X_mem {O σ A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] [Algebra.IsIntegral O A] (I : Ideal O)
    (hI : ∀ c : O, ¬ IsUnit c → ∃ n : ℕ, c ^ n ∈ I) (π : MvPowerSeries σ O →ₐ[O] A)
    (hπ : Function.Surjective π) (j : σ) :
    ∃ M : ℕ, π (MvPowerSeries.X j) ^ M ∈ I.map (algebraMap O A) := by
  change π (MvPowerSeries.X j) ∈ (I.map (algebraMap O A)).radical
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro (P : Ideal A) ⟨hIP, hP⟩
  have hmax : (Ideal.comap (algebraMap O A) P).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal O ≤ Ideal.comap (algebraMap O A) P := by
      intro c hc
      obtain ⟨n, hn⟩ := hI c hc
      have : c ^ n ∈ Ideal.comap (algebraMap O A) P := (Ideal.map_le_iff_le_comap.1 hIP) hn
      exact (Ideal.comap_isPrime _ P).mem_of_pow_mem n this
    have := (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_isPrime _ P).ne_top hle
    rw [← this]
    exact IsLocalRing.maximalIdeal.isMaximal O
  have hPm : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hmax
  have h2 : (Ideal.comap (π : MvPowerSeries σ O →+* A) P).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (π : MvPowerSeries σ O →+* A) hπ
  have h3 := IsLocalRing.eq_maximalIdeal h2
  have h4 : (MvPowerSeries.X j : MvPowerSeries σ O) ∈ IsLocalRing.maximalIdeal _ := by
    intro hu
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at hu
    exact not_isUnit_zero hu
  rw [← h3] at h4
  exact h4
private theorem pow_mem_map {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] (I : Ideal O) (e : A →ₐ[O] B) {x : A}
    (h : ∃ M : ℕ, x ^ M ∈ I.map (algebraMap O A)) :
    ∃ M : ℕ, e x ^ M ∈ I.map (algebraMap O B) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, ?_⟩
  have := Ideal.mem_map_of_mem (e : A →+* B) hM
  rw [Ideal.map_map, AlgHom.comp_algebraMap, map_pow] at this
  exact this
end SeriesTensor
end GlobalTheory
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
private theorem SeriesTensor.ev_pt_X {R : Type} [CommRing R] {d : ℕ} (k : Fin 2) (i : Fin d) :
    ev (n := 2) ![pt R d k] (MvPowerSeries.X ((0 : Fin 1), i)) = MvPowerSeries.X (k, i) := by
  unfold ev
  rw [MvPowerSeries.subst_X]
  · rfl
  · refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
    rintro ⟨a, l⟩
    fin_cases a
    exact MvPowerSeries.constantCoeff_X _
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open SeriesTensor
namespace GlobalTheory
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (J : Ideal (PS O 1 d)), Module.Free O (PS O 1 d ⧸ J) → Module.Finite O (PS O 1 d ⧸ J) → ∀ f : PS O 2 d, ∃ (m : ℕ) (g h : Fin m → PS O 1 d), ∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O), (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) → (∀ u ∈ J, φ u = 0) → (∀ u ∈ J, φ' u = 0) → Φ f = ∑ i, φ (g i) * φ' (h i) := by
  intro p _ C _ _ _ v O _ _ hv _ _ d J hfree hfin f
  have hdom : IsDomain O := hv.hom_inj.isDomain _
  have := ValuationRing.of_integers v hv
  set I : Ideal O := Ideal.span {(p : O)}
  have hp0 : algebraMap O C (p : O) ≠ 0 := by
    rw [map_natCast]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hI : ∀ c : O, ¬ IsUnit c → ∃ n : ℕ, c ^ n ∈ I := fun c hc => exists_pow_mem hv hp0 hc
  let Q := PS O 1 d ⧸ J
  let π : PS O 1 d →ₐ[O] Q := Ideal.Quotient.mkₐ O J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective O J
  let A := Q ⊗[O] Q
  have hA : IsAdicComplete (I.map (algebraMap O A)) A := by
    rw [IsAdicComplete.map_algebraMap_iff]
    exact isAdicComplete_of_basis (Module.Free.chooseBasis O A) I
  let e : Fin 2 → (Q →ₐ[O] A) :=
    ![Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]
  let a : Fin 2 × Fin d → A := fun q => e q.1 (π (MvPowerSeries.X (0, q.2)))
  have ha : ∀ q, ∃ M : ℕ, a q ^ M ∈ I.map (algebraMap O A) := fun q =>
    pow_mem_map (A := Q) (B := A) I (e q.1) (exists_pow_X_mem (A := Q) I hI π hπ (0, q.2))
  obtain ⟨Ψ, hΨ⟩ := (mvPowerSeries_eval_of_pow_mem A _ _ a ha).1 hA O
  obtain ⟨m, x, y, hxy⟩ := TensorProduct.exists_sum_tmul_eq (Ψ f)
  choose g hg using fun i => hπ (x i)
  choose h hh using fun i => hπ (y i)
  refine ⟨m, g, h, fun Φ φ φ' h0 h1 hJ hJ' => ?_⟩
  let ψ : Q →ₐ[O] O := Ideal.Quotient.liftₐ J φ hJ
  let ψ' : Q →ₐ[O] O := Ideal.Quotient.liftₐ J φ' hJ'
  let T : A →ₐ[O] O := Algebra.TensorProduct.lift ψ ψ' fun _ _ => Commute.all _ _
  have hsurj : Function.Surjective Φ := fun c => ⟨algebraMap O _ c, Φ.commutes c⟩
  have hnil := fun q => exists_pow_X_mem I hI Φ hsurj q
  have hH : IsHausdorff (I.map (algebraMap O O)) O := by
    rw [IsHausdorff.map_algebraMap_iff]
    infer_instance
  have key := (mvPowerSeries_eval_of_pow_mem O _ _ _ hnil).2 hH O
    (Φ : PS O 2 d →+* O) (T.comp Ψ : PS O 2 d →+* O)
    (fun t => (Φ.commutes t).trans ((T.comp Ψ).commutes t).symm) (fun _ => rfl) (by
      rintro ⟨k, i⟩
      change T (Ψ (MvPowerSeries.X (k, i))) = _
      rw [hΨ, ← ev_pt_X k i]
      fin_cases k
      · refine Eq.trans ?_ (h0 _).symm
        change T (π _ ⊗ₜ 1) = _
        rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
        rfl
      · refine Eq.trans ?_ (h1 _).symm
        change T (1 ⊗ₜ π _) = _
        rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
        rfl)
  have hf : Φ f = T (Ψ f) := RingHom.congr_fun key f
  rw [hf, hxy, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hg, ← hh]
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
end GlobalTheory
