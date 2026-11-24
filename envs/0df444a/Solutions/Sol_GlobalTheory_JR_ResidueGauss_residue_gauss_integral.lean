-- Prove2me | solution 1 for GlobalTheory.JR.ResidueGauss.residue_gauss_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:49.789089+00:00
-- url     : https://prove2.me/submissions/e4b5691e-ac36-4109-92a1-418857ff3578

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGaussIntegralNormForm
import Theorems.Thm_GlobalTheory_JR_ResidueGauss_setIntegral_addChar_eq_zero
import Theorems.Thm_GlobalTheory_JR_ResidueGauss_setIntegral_comp_mul_unit
import Theorems.Thm_GlobalTheory_JR_ResidueGauss_setIntegral_swap_of_continuous
import Theorems.Thm_GlobalTheory_JR_ResidueGauss_algebraMap_continuous_isCompact_preimage
import Theorems.Thm_GlobalTheory_JR_ResidueGauss_residue_algebra
import Theorems.Thm_GlobalTheory_JR_EtMeas_absK_unit
import Theorems.Thm_GlobalTheory_JR_EtMeas_continuous_NL
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure
import Theorems.Thm_GlobalTheory_StdChar_psi_conductor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ResidueGauss
set_option maxHeartbeats 1000000
namespace GlobalTheory.JR.ResidueGauss
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → IsField A.K → IsField A.L → ∀ (O : Subring A.L) (ϖ : A.Kˣ), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) → μ {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z} = ENNReal.ofReal (A.absK (ϖ : A.K) ^ 2) * μ (O : Set A.L) → ∀ a : A.K, (∀ s : A.K, algebraMap A.K A.L s ∈ O → A.psiK ψ (a * ϖ * s) = 1) → (∃ s : A.K, algebraMap A.K A.L s ∈ O ∧ A.psiK ψ (a * s) ≠ 1) → ∫ y in (O : Set A.L), A.psiK ψ (a * A.NL y) ∂μ = -((A.absK (ϖ : A.K) : ℝ) : ℂ) * (((μ (O : Set A.L)).toReal : ℝ) : ℂ) := by
  intro F E _ _ _ _ U A ψ μ hψ hμ hK hL O ϖ hOo hOc hOs hϖO hϖnu hdich hnorm hvol a ha hna
  classical
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  obtain ⟨-, hinj, hN, -, -⟩ := Et.quadratic_structure F E A
  obtain ⟨hιc, hιK⟩ := algebraMap_continuous_isCompact_preimage A
  obtain ⟨hψlc, hψn, -⟩ := (GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ
  obtain ⟨alg1, alg2⟩ := residue_algebra hK hinj A.NL hN O ϖ hOs hϖO hϖnu hdich hnorm
  set ι := algebraMap A.K A.L with hι
  set p : A.K := (ϖ : A.K) with hp

  set f : A.K → ℂ := fun t => A.psiK ψ (a * t) with hfdef
  have hfadd : ∀ x y, f (x + y) = f x * f y := by
    intro x y
    simp only [hfdef, Et.psiK, mul_add, map_add, AddChar.map_add_eq_mul]
  have hfc : Continuous f := by
    have htr : Continuous (fun t : A.K => Algebra.trace F A.K t) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact hψlc.continuous.comp (htr.comp (continuous_const.mul continuous_id))
  have hfn : ∀ t, ‖f t‖ = 1 := fun t => hψn _

  set OK : Subring A.K := O.comap ι with hOK
  have memOK : ∀ s, s ∈ OK ↔ ι s ∈ O := fun s => Iff.rfl
  set PK : Set A.K := ϖ • (OK : Set A.K) with hPK
  have memPK : ∀ s, s ∈ PK ↔ ∃ t, ι t ∈ O ∧ s = p * t := by
    intro s
    simp only [hPK, Set.mem_smul_set, SetLike.mem_coe, memOK, Units.smul_def, smul_eq_mul]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  set UK : Set A.K := (OK : Set A.K) \ PK with hUK
  set PL : Set A.L := {y | ∃ z ∈ O, y = ι p * z} with hPL
  set UL : Set A.L := (O : Set A.L) \ PL with hUL
  have hPKsub : PK ⊆ OK := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := (memPK s).1 hs
    exact (memOK _).2 (by rw [map_mul]; exact O.mul_mem hϖO ht)
  have hPLsub : PL ⊆ O := by
    rintro y ⟨z, hz, rfl⟩
    exact O.mul_mem hϖO hz
  have hPLeq : PL = (fun z => ι p * z) '' (O : Set A.L) := by
    ext y; simp only [hPL, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

  have hOKo : IsOpen (OK : Set A.K) := hOo.preimage hιc
  have hOKc : IsCompact (OK : Set A.K) := hιK _ hOc
  have hPKc : IsCompact PK := by
    rw [hPK]; exact hOKc.image (continuous_const_smul ϖ)
  have hPLc : IsCompact PL := by
    rw [hPLeq]; exact hOc.image (continuous_const.mul continuous_id)
  have hOKm : MeasurableSet (OK : Set A.K) := hOKc.isClosed.measurableSet
  have hPKm : MeasurableSet PK := hPKc.isClosed.measurableSet
  have hUKm : MeasurableSet UK := hOKm.diff hPKm
  have hOm : MeasurableSet (O : Set A.L) := hOc.isClosed.measurableSet
  have hPLm : MeasurableSet PL := hPLc.isClosed.measurableSet
  have hULm : MeasurableSet UL := hOm.diff hPLm
  have h1UK : (1 : A.K) ∈ UK := by
    refine ⟨(memOK 1).2 (by rw [map_one]; exact O.one_mem), fun h => hϖnu ?_⟩
    obtain ⟨t, ht, e⟩ := (memPK 1).1 h
    exact ⟨ι t, ht, by rw [← map_mul, ← e, map_one]⟩
  have hUKo : IsOpen UK := hOKo.sdiff hPKc.isClosed

  set μK : Measure A.K := Measure.addHaar with hμK
  set x : ℝ := A.absK p with hxdef
  have hx : x = (distribHaarChar A.K ϖ : ℝ) := EtMeas.absK_unit A ϖ
  have hx0 : 0 ≤ x := by rw [hx]; exact NNReal.coe_nonneg _
  have hOKT : μK OK ≠ ⊤ := hOKc.measure_lt_top.ne
  have hPKT : μK PK ≠ ⊤ := hPKc.measure_lt_top.ne
  have hUKT : μK UK ≠ ⊤ := (measure_mono Set.sdiff_subset).trans_lt hOKc.measure_lt_top |>.ne
  have hUK0 : μK UK ≠ 0 := hUKo.measure_ne_zero μK ⟨1, h1UK⟩
  have hOT : μ O ≠ ⊤ := hOc.measure_lt_top.ne
  have hO0 : μ O ≠ 0 := hOo.measure_ne_zero μ ⟨1, O.one_mem⟩
  set mK : ℝ := (μK OK).toReal with hmK
  set M : ℝ := (μ O).toReal with hM
  have hmPK : (μK PK).toReal = x * mK := by
    rw [hPK, ← distribHaarChar_mul, ENNReal.toReal_mul, hx]; rfl
  have hmUK : (μK UK).toReal = mK - x * mK := by
    rw [hUK, measure_sdiff hPKsub hPKm.nullMeasurableSet hPKT, ENNReal.toReal_sub_of_le (measure_mono hPKsub) hOKT,
      hmPK]
  have hmPL : (μ PL).toReal = x ^ 2 * M := by
    rw [hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  have hmUL : (μ UL).toReal = M - x ^ 2 * M := by
    rw [hUL, measure_sdiff hPLsub hPLm.nullMeasurableSet (measure_ne_top_of_subset hPLsub hOT),
      ENNReal.toReal_sub_of_le (measure_mono hPLsub) hOT, hmPL]
  have hmUKpos : 0 < (μK UK).toReal := ENNReal.toReal_pos hUK0 hUKT

  have hf1 : ∀ m, ι m ∈ O → f (p * m) = 1 := by
    intro m hm
    simp only [hfdef]
    rw [← mul_assoc]; exact ha m hm
  have hNp : ∀ z, A.NL (ι p * z) = p * (p * A.NL z) := by
    intro z
    apply hinj
    rw [hN, map_mul, map_mul, hN, star_mul', A.star_K]
    ring

  set I : ℂ := ∫ y in (O : Set A.L), f (A.NL y) ∂μ with hIdef
  have hI1 : ∀ s ∈ UK, ∫ y in (O : Set A.L), f (s * A.NL y) ∂μ = I := by
    intro s hs
    obtain ⟨-, w, hw, v, hv, hwv, hNw⟩ :=
      alg2 s ((memOK s).1 hs.1) (fun ⟨t, ht, e⟩ => hs.2 ((memPK s).2 ⟨t, ht, e⟩))
    have key : ∀ y, A.NL (w * y) = s * A.NL y := by
      intro y
      apply hinj
      rw [hN, map_mul, hN, ← hNw, hN, star_mul']
      ring
    have := setIntegral_comp_mul_unit μ (O : Set A.L) w v hwv hO0 hOT (fun y hy => O.mul_mem hw hy)
      (fun y hy => O.mul_mem hv hy) (fun y => f (A.NL y))
    simp only [key] at this
    exact this

  have hIOK : IntegrableOn f OK μK := hfc.continuousOn.integrableOn_compact hOKc
  have hintOK : ∫ s in (OK : Set A.K), f s ∂μK = 0 := by
    obtain ⟨s₀, hs₀, hne⟩ := hna
    exact setIntegral_addChar_eq_zero μK OK.toAddSubgroup f hfadd s₀ hs₀ hne
  have hintPK : ∫ s in PK, f s ∂μK = (μK PK).toReal := by
    rw [setIntegral_congr_fun hPKm (g := fun _ => (1 : ℂ)) (fun s hs => by
      obtain ⟨t, ht, rfl⟩ := (memPK s).1 hs; exact hf1 t ht)]
    simp [Measure.real]
  have hintUK : ∫ s in UK, f s ∂μK = -((μK PK).toReal : ℂ) := by
    rw [hUK, setIntegral_sdiff hPKm hIOK hPKsub, hintOK, hintPK, zero_sub]
  have hUKmul : ∀ t ∈ UK, ∫ s in UK, f (s * t) ∂μK = -((μK PK).toReal : ℂ) := by
    intro t ht
    obtain ⟨⟨r, hr, htr⟩, -⟩ :=
      alg2 t ((memOK t).1 ht.1) (fun ⟨m, hm, e⟩ => ht.2 ((memPK t).2 ⟨m, hm, e⟩))
    have hcl : ∀ u v : A.K, u * v = 1 → ι u ∈ O → ι v ∈ O → ∀ s ∈ UK, u * s ∈ UK := by
      intro u v huv hu hv s hs
      refine ⟨(memOK _).2 (by rw [map_mul]; exact O.mul_mem hu hs.1), fun h => hs.2 ?_⟩
      obtain ⟨m, hm, e⟩ := (memPK _).1 h
      refine (memPK s).2 ⟨v * m, by rw [map_mul]; exact O.mul_mem hv hm, ?_⟩
      calc s = v * (u * s) := by rw [← mul_assoc, mul_comm v u, huv, one_mul]
        _ = p * (v * m) := by rw [e]; ring
    have := setIntegral_comp_mul_unit μK UK t r htr hUK0 hUKT (hcl t r htr ht.1 hr)
      (hcl r t (by rw [mul_comm]; exact htr) hr ht.1) f
    simp only [mul_comm _ t]
    rw [this, hintUK]
  have hJP : ∀ y ∈ PL, ∫ s in UK, f (s * A.NL y) ∂μK = (μK UK).toReal := by
    rintro y ⟨z, hz, rfl⟩
    rw [setIntegral_congr_fun hUKm (g := fun _ => (1 : ℂ)) (fun s hs => by
      simp only [hNp]
      rw [show s * (p * (p * A.NL z)) = p * (s * p * A.NL z) by ring]
      refine hf1 _ ?_
      rw [map_mul, map_mul, hN]
      exact O.mul_mem (O.mul_mem hs.1 hϖO) (O.mul_mem hz (hOs z hz)))]
    simp [Measure.real]
  have hJU : ∀ y ∈ UL, ∫ s in UK, f (s * A.NL y) ∂μK = -((μK PK).toReal : ℂ) := by
    intro y hy
    obtain ⟨h1, h2, -⟩ := alg1 y hy.1 hy.2
    exact hUKmul _ ⟨(memOK _).2 h1, fun h => h2 ((memPK _).1 h)⟩

  have hswap := setIntegral_swap_of_continuous μK μ UK (O : Set A.L) hUKT hOT (fun s y => f (s * A.NL y))
    (hfc.comp (continuous_fst.mul ((EtMeas.continuous_NL A).comp continuous_snd))) (fun s y => (hfn _).le)
  have hLHS : ∫ s in UK, ∫ y in (O : Set A.L), f (s * A.NL y) ∂μ ∂μK = (μK UK).toReal * I := by
    rw [setIntegral_congr_fun hUKm (g := fun _ => I) hI1]
    simp [Measure.real]
  have hOsplit : (O : Set A.L) = PL ∪ UL := (Set.union_sdiff_cancel hPLsub).symm
  have hRHS : ∫ y in (O : Set A.L), ∫ s in UK, f (s * A.NL y) ∂μK ∂μ =
      (μ PL).toReal * (μK UK).toReal + (μ UL).toReal * (-((μK PK).toReal : ℂ)) := by
    have hPLT : μ PL ≠ ⊤ := measure_ne_top_of_subset hPLsub hOT
    have hULT : μ UL ≠ ⊤ := measure_ne_top_of_subset Set.sdiff_subset hOT
    have i1 : IntegrableOn (fun y => ∫ s in UK, f (s * A.NL y) ∂μK) PL μ :=
      (integrableOn_const hPLT).congr_fun (fun y hy => (hJP y hy).symm) hPLm
    have i2 : IntegrableOn (fun y => ∫ s in UK, f (s * A.NL y) ∂μK) UL μ :=
      (integrableOn_const hULT).congr_fun (fun y hy => (hJU y hy).symm) hULm
    rw [hOsplit, setIntegral_union Set.disjoint_sdiff_right hULm i1 i2,
      setIntegral_congr_fun hPLm hJP, setIntegral_congr_fun hULm hJU]
    simp [Measure.real]
  rw [hLHS, hRHS] at hswap
  have hne : ((μK UK).toReal : ℂ) ≠ 0 := by exact_mod_cast hmUKpos.ne'
  apply mul_left_cancel₀ hne
  rw [hswap, hmUK, hmPL, hmUL, hmPK]
  push_cast
  ring
end GlobalTheory.JR.ResidueGauss
