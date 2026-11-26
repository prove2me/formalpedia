-- Prove2me | solution 1 for Kyprianou.Ch04.predictableVersionCutoffRawEnergyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:38:07.044787+00:00
-- url     : https://prove2.me/submissions/ccae7eb7-98fc-4324-aeca-a8bbf95df276

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_boundedPredictableKernelDifferenceEnergyV1
import Theorems.Thm_Kyprianou_Ch04_cutoffPredictableTerminalCertificateV1
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Apply the two-kernel physical isometry and transfer both original cutoffs on their common full-measure event. -/
theorem solution :
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite triplet.levyMeasure]
    (N : PoissonRandomMeasure.{0,0,0} P triplet.levyMeasure)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P triplet.levyMeasure F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun ω => N.N ω D))
    (fSpace : ℝ → ℝ → ℝ)
    (hJoint : ContinuousOn (fun z : ℝ × ℝ => fSpace z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (K : ℝ) (hK : 0 < K)
    (hBound : ∀ s x : ℝ, 0 ≤ s → |fSpace s x| ≤ K)
    (XepsLeft V : ℝ → NNReal → Omega → ℝ)
    (hV : ∀ e : ℝ, 0 < e → e < 1 → IsStronglyPredictable F (V e))
    (hEq : ∀ e : ℝ, 0 < e → e < 1 →
      ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → V e t ω = XepsLeft e t ω),
    ∀ (T : NNReal), 0 < T ->
          ∀ (M : Real -> NNReal -> Omega -> Real),
            (∀ epsilon : Real, 0 < epsilon -> epsilon < 1 ->
              (∀ t omega, M epsilon t omega = (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
        {x : Real | epsilon < |x| ∧ |x| < 1},
        z.2 * fSpace z.1 (XepsLeft epsilon (Real.toNNReal z.1) omega)
        ∂(N.N omega)) -
      (∫ s in Set.Icc (0 : Real) (t : Real),
        (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1},
          x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega)
          ∂triplet.levyMeasure) ∂volume)) ∧
              MeasureTheory.Martingale (M epsilon) F P) ->
    ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      (∫ ω, (M a T ω - M b T ω)^2 ∂P) ≤
        (∫ ω, ∫ s in Set.Ioc (0 : ℝ) (T : ℝ),
          ∫ z, (({w : ℝ | a < |w| ∧ |w| < 1}).indicator
              (fun w => w * fSpace s (XepsLeft a s.toNNReal ω)) z -
            ({w : ℝ | b < |w| ∧ |w| < 1}).indicator
              (fun w => w * fSpace s (XepsLeft b s.toNNReal ω)) z)^2
              ∂triplet.levyMeasure ∂volume ∂P) := by
  intro Ω m P hP F triplet hSigma N hFuture hPast fSpace hJoint K hK hBound
    L V hV hEq T hT M hM a b ha hab hb
  let ν := triplet.levyMeasure
  let B (e : ℝ) : Set ℝ := {x | e < |x| ∧ |x| < 1}
  have hB (e : ℝ) : MeasurableSet (B e) :=
    (measurableSet_lt measurable_const measurable_id.abs).inter
      (measurableSet_lt measurable_id.abs measurable_const)
  have hFin (e : ℝ) (he : 0 < e) : ν (B e) < ⊤ :=
    (measure_mono (show B e ⊆ {z | e ≤ |z|} from fun z hz => hz.1.le)).trans_lt
      (triplet.levyMeasure_isLevyMeasure.measure_setOf_abs_ge_lt_top he)
  let W (e : ℝ) (p : NNReal × Ω) := fSpace (p.1 : ℝ) (V e p.1 p.2)
  let g (e : ℝ) (p : (NNReal × Ω) × ℝ) :=
    (B e).indicator (fun z => z * W e p.1) p.2
  let U := Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)
  let q := fun (ω : Ω) (z : ℝ × ℝ) => ((z.1.toNNReal,ω),z.2)
  let J := fun (k : (NNReal × Ω) × ℝ → ℝ) ω =>
    (∫ z in U, k (q ω z) ∂(N.N ω)) - ∫ z in U, k (q ω z) ∂referenceIntensity ν
  have hG (e : ℝ) (he : 0 < e) (he1 : e < 1) :
      Measurable[F.predictable.prod inferInstance] (g e) ∧
        (∀ p, ‖g e p‖ ≤ K) ∧ (∀ p, p.2 ∉ B e → g e p = 0) ∧
        (∀ᵐ ω ∂P, M e T ω = J (g e) ω) :=
    Kyprianou.Ch04.cutoffPredictableTerminalCertificateV1 P ν F N T e K hK.le
      (hFin e he) fSpace hJoint hBound (L e) (V e) (hV e he he1)
      (hEq e he he1) (M e T) ((hM e he he1).1 T)
  have ha1 := hab.trans hb
  have hb0 := ha.trans hab
  have hTwo := Kyprianou.Ch04.boundedPredictableKernelDifferenceEnergyV1 P ν F N
    hFuture hPast T (B a) (hB a) (hFin a ha) (g a) (g b)
    (hG a ha ha1).1 (hG b hb0 hb).1 K
    (fun p => ⟨(hG a ha ha1).2.1 p,(hG b hb0 hb).2.1 p⟩)
    (fun p hp => ⟨(hG a ha ha1).2.2.1 p hp,
      (hG b hb0 hb).2.2.1 p (fun h => hp ⟨hab.trans h.1,h.2⟩)⟩)
  have hLeft : (∫ ω, (M a T ω - M b T ω)^2 ∂P) =
      ∫ ω, (J (g a) ω - J (g b) ω)^2 ∂P := by
    apply integral_congr_ae
    filter_upwards [(hG a ha ha1).2.2.2,(hG b hb0 hb).2.2.2] with ω h1 h2
    rw [h1,h2]
  rw [hLeft,hTwo]
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [hEq a ha ha1,hEq b hb0 hb] with ω h1 h2
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  have ht : 0 < s.toNNReal := Real.toNNReal_pos.mpr hs.1
  simp only [g,W,B,ν,Real.coe_toNNReal s hs.1.le,h1 _ ht,h2 _ ht]
