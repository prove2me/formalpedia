-- Prove2me | solution 1 for Kyprianou.Ch03.spectrallyNegative_canonicalEsscherUncompleted
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T21:13:27.2021+00:00
-- url     : https://prove2.me/submissions/132f6c42-bd3a-42e3-9b93-ef6944d2e561

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Theorems.Thm_levy_foundations_kolmogorovExtension_exists

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03.CanonicalEsscherUncompletedProof

/-! ### 1. Canonical càdlàg path space with no positive jumps -/

private structure CadlagSNL where
  val : NNReal → ℝ
  val_zero : val 0 = 0
  rightCont : ∀ t : NNReal, ContinuousWithinAt val (Ici t) t
  leftLim : ∀ t : NNReal, 0 < t → ∃ l : ℝ, Tendsto val (𝓝[<] t) (𝓝 l)
  noPosJumps : ∀ (t : NNReal) (l : ℝ), 0 < t → Tendsto val (𝓝[<] t) (𝓝 l) → val t ≤ l

private def cadlagZero : CadlagSNL where
  val := fun _ => 0
  val_zero := rfl
  rightCont := fun _ => continuousWithinAt_const
  leftLim := fun _ _ => ⟨0, tendsto_const_nhds⟩
  noPosJumps := fun t l ht hl => by
    let seq : ℕ → NNReal := fun k => t * ((k + 1 : NNReal) / (k + 2 : NNReal))
    have hseq_lt : ∀ k : ℕ, seq k < t := fun k => by
      dsimp only [seq]
      have hlt1 : ((k + 1 : NNReal) / (k + 2 : NNReal)) < 1 := by
        rw [div_lt_one (by positivity)]
        exact_mod_cast Nat.lt_succ_self (k + 1)
      simpa using mul_lt_mul_of_pos_left hlt1 ht
    have hseq_tend : Tendsto seq atTop (𝓝[<] t) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall hseq_lt⟩
      have hdiv : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / ((k : ℝ) + 2)) atTop (𝓝 1) := by
        have hrew : (fun k : ℕ => ((k : ℝ) + 1) / ((k : ℝ) + 2)) =
            fun k : ℕ => 1 - 1 / ((k : ℝ) + 2) := by
          ext k
          have hne : (k : ℝ) + 2 ≠ 0 := by positivity
          field_simp [hne]; ring
        rw [hrew]
        have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) atTop (𝓝 0) := by
          have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
          refine h1.congr fun k => ?_
          change (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) = (1 : ℝ) / ((k : ℝ) + 2)
          push_cast; ring
        simpa using tendsto_const_nhds.sub h0
      exact NNReal.tendsto_coe.mp (by simpa [seq, mul_one] using hdiv.const_mul (t : ℝ))
    have h0 : (0 : ℝ) = l := tendsto_nhds_unique tendsto_const_nhds (hl.comp hseq_tend)
    linarith

@[instance_reducible]
private def cadlagMS : MeasurableSpace CadlagSNL :=
  MeasurableSpace.comap CadlagSNL.val inferInstance

private lemma measurable_cadlagVal :
    @Measurable CadlagSNL (NNReal → ℝ) cadlagMS inferInstance CadlagSNL.val :=
  Measurable.of_comap_le le_rfl

private lemma measurable_toCadlagSNL {α : Type*} [mα : MeasurableSpace α]
    {g : α → CadlagSNL}
    (hg : ∀ t : NNReal, Measurable (fun a => (g a).val t)) :
    @Measurable α CadlagSNL mα cadlagMS g := by
  rw [show cadlagMS = MeasurableSpace.comap CadlagSNL.val inferInstance from rfl]
  rw [measurable_iff_comap_le, MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.mp (measurable_pi_lambda _ hg)

private def cadlagFiltr : Filtration NNReal cadlagMS where
  seq := PerfCorrMSQ.natFiltr (fun t (p : CadlagSNL) => p.val t)
  mono' := fun _ _ hst => iSup₂_mono' fun u hu => ⟨u, hu.trans hst, le_rfl⟩
  le' := fun s => iSup₂_le fun u _ => by
    have h1 : @Measurable CadlagSNL ℝ cadlagMS inferInstance (fun p => p.val u) :=
      (measurable_pi_apply u).comp measurable_cadlagVal
    exact measurable_iff_comap_le.mp h1

private lemma natFiltr_le_pi (t : NNReal) :
    PerfCorrMSQ.natFiltr (fun (s : NNReal) (f : NNReal → ℝ) => f s) t ≤
      (inferInstance : MeasurableSpace (NNReal → ℝ)) :=
  iSup₂_le fun u _ => measurable_iff_comap_le.mp (measurable_pi_apply u)

private lemma natFiltr_eval_eq_generateFrom_cylinders (t : NNReal) :
    PerfCorrMSQ.natFiltr (fun (s : NNReal) (f : NNReal → ℝ) => f s) t =
      MeasurableSpace.generateFrom
        {A : Set (NNReal → ℝ) | ∃ (I : Finset NNReal) (_ : ∀ s ∈ I, s ≤ t)
          (E : Set (∀ _ : I, ℝ)), MeasurableSet E ∧ A = I.restrict ⁻¹' E} := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun u hu => ?_
    rintro A ⟨B, hB, rfl⟩
    refine MeasurableSpace.measurableSet_generateFrom ?_
    let I : Finset NNReal := {u}
    have hI : ∀ s ∈ I, s ≤ t := fun s hs => by
      rw [Finset.mem_singleton.mp hs]; exact hu
    let E : Set (∀ _ : I, ℝ) := (fun g : ∀ _ : I, ℝ => g ⟨u, Finset.mem_singleton_self u⟩) ⁻¹' B
    have hE : MeasurableSet E :=
      (measurable_pi_apply (⟨u, Finset.mem_singleton_self u⟩ : I)) hB
    exact ⟨I, hI, E, hE, rfl⟩
  · refine MeasurableSpace.generateFrom_le ?_
    rintro A ⟨I, hI, E, hE, rfl⟩
    have hres : @Measurable (NNReal → ℝ) (∀ _ : I, ℝ)
        (PerfCorrMSQ.natFiltr (fun (s : NNReal) (f : NNReal → ℝ) => f s) t) inferInstance
        I.restrict := by
      refine @measurable_pi_lambda (NNReal → ℝ) I (fun _ => ℝ)
        (PerfCorrMSQ.natFiltr (fun (s : NNReal) (f : NNReal → ℝ) => f s) t) _ _ fun s => ?_
      have hle : MeasurableSpace.comap (fun f : NNReal → ℝ => f s.1) inferInstance ≤
          PerfCorrMSQ.natFiltr (fun (s : NNReal) (f : NNReal → ℝ) => f s) t :=
        le_iSup₂_of_le s.1 (hI s.1 s.2) le_rfl
      exact measurable_iff_comap_le.mpr hle
    exact hres hE

private lemma isPiSystem_cylinders (t : NNReal) :
    IsPiSystem
      {A : Set (NNReal → ℝ) | ∃ (I : Finset NNReal) (_ : ∀ s ∈ I, s ≤ t)
        (E : Set (∀ _ : I, ℝ)), MeasurableSet E ∧ A = I.restrict ⁻¹' E} := by
  classical
  rintro A₁ ⟨I₁, hI₁, E₁, hE₁, rfl⟩ A₂ ⟨I₂, hI₂, E₂, hE₂, rfl⟩ _
  let I : Finset NNReal := I₁ ∪ I₂
  have hI : ∀ s ∈ I, s ≤ t := fun s hs => by
    rcases Finset.mem_union.mp hs with h1 | h2
    · exact hI₁ s h1
    · exact hI₂ s h2
  have h1 : I₁ ⊆ I := Finset.subset_union_left
  have h2 : I₂ ⊆ I := Finset.subset_union_right
  let E : Set (∀ _ : I, ℝ) :=
    Finset.restrict₂ (π := fun _ : NNReal => ℝ) h1 ⁻¹' E₁ ∩
      Finset.restrict₂ (π := fun _ : NNReal => ℝ) h2 ⁻¹' E₂
  have hE : MeasurableSet E :=
    ((Finset.measurable_restrict₂ (X := fun _ : NNReal => ℝ) h1) hE₁).inter
      ((Finset.measurable_restrict₂ (X := fun _ : NNReal => ℝ) h2) hE₂)
  refine ⟨I, hI, E, hE, ?_⟩
  ext f
  exact Iff.rfl

private lemma cadlagFiltr_eq_generateFrom_cylinders (t : NNReal) :
    cadlagFiltr t =
      MeasurableSpace.generateFrom
        {A : Set CadlagSNL | ∃ (I : Finset NNReal) (_ : ∀ s ∈ I, s ≤ t)
          (E : Set (∀ _ : I, ℝ)), MeasurableSet E ∧
            A = (fun p : CadlagSNL => I.restrict p.val) ⁻¹' E} := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun u hu => ?_
    rintro A ⟨B, hB, rfl⟩
    refine MeasurableSpace.measurableSet_generateFrom ?_
    let I : Finset NNReal := {u}
    have hI : ∀ s ∈ I, s ≤ t := fun s hs => by
      rw [Finset.mem_singleton.mp hs]; exact hu
    let E : Set (∀ _ : I, ℝ) := (fun g : ∀ _ : I, ℝ => g ⟨u, Finset.mem_singleton_self u⟩) ⁻¹' B
    have hE : MeasurableSet E :=
      (measurable_pi_apply (⟨u, Finset.mem_singleton_self u⟩ : I)) hB
    exact ⟨I, hI, E, hE, rfl⟩
  · refine MeasurableSpace.generateFrom_le ?_
    rintro A ⟨I, hI, E, hE, rfl⟩
    have hres : @Measurable CadlagSNL (∀ _ : I, ℝ) (cadlagFiltr t) inferInstance
        (fun p : CadlagSNL => I.restrict p.val) := by
      refine @measurable_pi_lambda CadlagSNL I (fun _ => ℝ) (cadlagFiltr t) _ _ fun s => ?_
      have hle : MeasurableSpace.comap (fun p : CadlagSNL => p.val s.1) inferInstance ≤
          cadlagFiltr t :=
        le_iSup₂_of_le s.1 (hI s.1 s.2) le_rfl
      exact measurable_iff_comap_le.mpr hle
    exact hres hE

private lemma isPiSystem_cadlagCylinders (t : NNReal) :
    IsPiSystem
      {A : Set CadlagSNL | ∃ (I : Finset NNReal) (_ : ∀ s ∈ I, s ≤ t)
        (E : Set (∀ _ : I, ℝ)), MeasurableSet E ∧
          A = (fun p : CadlagSNL => I.restrict p.val) ⁻¹' E} := by
  classical
  rintro A₁ ⟨I₁, hI₁, E₁, hE₁, rfl⟩ A₂ ⟨I₂, hI₂, E₂, hE₂, rfl⟩ _
  let I : Finset NNReal := I₁ ∪ I₂
  have hI : ∀ s ∈ I, s ≤ t := fun s hs => by
    rcases Finset.mem_union.mp hs with h1 | h2
    · exact hI₁ s h1
    · exact hI₂ s h2
  have h1 : I₁ ⊆ I := Finset.subset_union_left
  have h2 : I₂ ⊆ I := Finset.subset_union_right
  let E : Set (∀ _ : I, ℝ) :=
    Finset.restrict₂ (π := fun _ : NNReal => ℝ) h1 ⁻¹' E₁ ∩
      Finset.restrict₂ (π := fun _ : NNReal => ℝ) h2 ⁻¹' E₂
  have hE : MeasurableSet E :=
    ((Finset.measurable_restrict₂ (X := fun _ : NNReal => ℝ) h1) hE₁).inter
      ((Finset.measurable_restrict₂ (X := fun _ : NNReal => ℝ) h2) hE₂)
  refine ⟨I, hI, E, hE, ?_⟩
  ext p
  exact Iff.rfl

/-! ### 2. Rational càdlàg + no-positive-jumps regularity on `[0, N]` -/

private abbrev RatDom (N : ℕ) := {q : ℚ // 0 ≤ q ∧ q ≤ (N : ℚ)}

private noncomputable def ratToNN {N : ℕ} (q : RatDom N) : NNReal :=
  Real.toNNReal (q.1 : ℝ)

private lemma ratToNN_coe {N : ℕ} (q : RatDom N) : (ratToNN q : ℝ) = (q.1 : ℝ) :=
  Real.coe_toNNReal (q.1 : ℝ) (Rat.cast_nonneg.mpr q.2.1)

private lemma ratToNN_le {N : ℕ} (q : RatDom N) : ratToNN q ≤ (N : NNReal) := by
  rw [← NNReal.coe_le_coe, ratToNN_coe, NNReal.coe_natCast]
  exact_mod_cast q.2.2

private def RatBounded (N : ℕ) (f : NNReal → ℝ) : Prop :=
  ∃ M : ℕ, ∀ q : RatDom N, |f (ratToNN q)| ≤ (M : ℝ)

private def RatNoOsc (N : ℕ) (f : NNReal → ℝ) : Prop :=
  ∀ a b : ℚ, a < b →
    ∃ m : ℕ, ∀ qs : Fin (2 * m + 1) → RatDom N,
      StrictMono (fun i => (qs i).1) →
      ¬ (∀ i : Fin (2 * m + 1),
        if Even i.val then f (ratToNN (qs i)) ≤ (a : ℝ) else (b : ℝ) ≤ f (ratToNN (qs i)))

private def RatNoPosJumps (N : ℕ) (f : NNReal → ℝ) : Prop :=
  ∀ k : ℕ, ∃ m : ℕ, ∀ q1 q2 : RatDom N,
    q1.1 < q2.1 → ((q2.1 : ℝ) - (q1.1 : ℝ)) < 1 / ((m : ℝ) + 1) →
      f (ratToNN q2) - f (ratToNN q1) ≤ 1 / ((k : ℝ) + 1)

private def RatZeroRightCont (N : ℕ) (f : NNReal → ℝ) : Prop :=
  ∀ k : ℕ, ∃ m : ℕ, ∀ q : RatDom N,
    (q.1 : ℝ) < 1 / ((m : ℝ) + 1) → |f (ratToNN q)| ≤ 1 / ((k : ℝ) + 1)

private def GoodN (N : ℕ) : Set (NNReal → ℝ) :=
  {f | RatBounded N f ∧ RatNoOsc N f ∧ RatNoPosJumps N f ∧ RatZeroRightCont N f}

private def Good : Set (NNReal → ℝ) :=
  ⋂ N : ℕ, GoodN (N + 1)

private lemma measurableSet_GoodN (N : ℕ) :
    MeasurableSet[PerfCorrMSQ.natFiltr (fun (s : NNReal) (f : NNReal → ℝ) => f s) (N : NNReal)]
      (GoodN N) := by
  have heval : ∀ q : RatDom N,
      @Measurable (NNReal → ℝ) ℝ
        (PerfCorrMSQ.natFiltr (fun (s : NNReal) (f : NNReal → ℝ) => f s) (N : NNReal)) inferInstance
        (fun f => f (ratToNN q)) := fun q =>
    measurable_iff_comap_le.mpr (le_iSup₂_of_le (ratToNN q) (ratToNN_le q) le_rfl)
  have h1 : MeasurableSet[PerfCorrMSQ.natFiltr (fun (s : NNReal) (f : NNReal → ℝ) => f s) (N : NNReal)]
      {f | RatBounded N f} := by
    have heq : {f | RatBounded N f} = ⋃ M : ℕ, ⋂ q : RatDom N, {f | |f (ratToNN q)| ≤ (M : ℝ)} := by
      ext f; simp [RatBounded]
    rw [heq]
    exact MeasurableSet.iUnion fun M => MeasurableSet.iInter fun q =>
      ((continuous_abs.measurable.comp (heval q)) measurableSet_Iic)
  have h2 : MeasurableSet[PerfCorrMSQ.natFiltr (fun (s : NNReal) (f : NNReal → ℝ) => f s) (N : NNReal)]
      {f | RatNoOsc N f} := by
    have heq : {f | RatNoOsc N f} =
        ⋂ a : ℚ, ⋂ b : ℚ, ⋂ (_ : a < b),
          ⋃ m : ℕ, ⋂ qs : Fin (2 * m + 1) → RatDom N,
            ⋂ (_ : StrictMono (fun i => (qs i).1)),
              (⋂ i : Fin (2 * m + 1),
                {f | if Even i.val then f (ratToNN (qs i)) ≤ (a : ℝ)
                     else (b : ℝ) ≤ f (ratToNN (qs i))})ᶜ := by
      ext f; simp [RatNoOsc]
    rw [heq]
    refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun m =>
      MeasurableSet.iInter fun qs => MeasurableSet.iInter fun _ =>
      (MeasurableSet.iInter fun i => ?_).compl
    by_cases he : Even i.val
    · simp only [he, ↓reduceIte]
      exact (heval (qs i)) measurableSet_Iic
    · simp only [he, ↓reduceIte]
      exact (heval (qs i)) measurableSet_Ici
  have h3 : MeasurableSet[PerfCorrMSQ.natFiltr (fun (s : NNReal) (f : NNReal → ℝ) => f s) (N : NNReal)]
      {f | RatNoPosJumps N f} := by
    have heq : {f | RatNoPosJumps N f} =
        ⋂ k : ℕ, ⋃ m : ℕ, ⋂ q1 : RatDom N, ⋂ q2 : RatDom N,
          ⋂ (_ : q1.1 < q2.1), ⋂ (_ : ((q2.1 : ℝ) - (q1.1 : ℝ)) < 1 / ((m : ℝ) + 1)),
            {f | f (ratToNN q2) - f (ratToNN q1) ≤ 1 / ((k : ℝ) + 1)} := by
      ext f; simp [RatNoPosJumps]
    rw [heq]
    exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun m =>
      MeasurableSet.iInter fun q1 => MeasurableSet.iInter fun q2 =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      ((heval q2).sub (heval q1)) measurableSet_Iic
  have h4 : MeasurableSet[PerfCorrMSQ.natFiltr (fun (s : NNReal) (f : NNReal → ℝ) => f s) (N : NNReal)]
      {f | RatZeroRightCont N f} := by
    have heq : {f | RatZeroRightCont N f} =
        ⋂ k : ℕ, ⋃ m : ℕ, ⋂ q : RatDom N,
          ⋂ (_ : (q.1 : ℝ) < 1 / ((m : ℝ) + 1)),
            {f | |f (ratToNN q)| ≤ 1 / ((k : ℝ) + 1)} := by
      ext f; simp [RatZeroRightCont]
    rw [heq]
    exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun m =>
      MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
      (continuous_abs.measurable.comp (heval q)) measurableSet_Iic
  exact h1.inter (h2.inter (h3.inter h4))

private lemma measurableSet_Good : MeasurableSet Good :=
  MeasurableSet.iInter fun N => natFiltr_le_pi (N + 1 : ℕ) _ (measurableSet_GoodN (N + 1))

/-! ### 3. Every `CadlagSNL` path lies in `GoodN N` (via compact cover + Lebesgue number) -/

private lemma cadlagSNL_local_ball (p : CadlagSNL) (t : NNReal) {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (l : ℝ), 0 < δ ∧ p.val t ≤ l ∧
      (∀ u : NNReal, t ≤ u → dist u t < δ → |p.val u - p.val t| < ε) ∧
      (∀ u : NNReal, u < t → dist u t < δ → |p.val u - l| < ε) := by
  have hrc := Metric.continuousWithinAt_iff.mp (p.rightCont t) ε hε
  rcases hrc with ⟨δ₁, hδ₁_pos, hδ₁⟩
  by_cases ht0 : t = 0
  · subst ht0
    refine ⟨δ₁, p.val 0, hδ₁_pos, le_rfl, ?_, ?_⟩
    · intro u hu hdu
      simpa [Real.dist_eq] using hδ₁ hu hdu
    · intro u hu _
      exact absurd hu (not_lt_of_ge bot_le)
  · have ht_pos : 0 < t := pos_iff_ne_zero.mpr ht0
    rcases p.leftLim t ht_pos with ⟨l, hl⟩
    have hno : p.val t ≤ l := p.noPosJumps t l ht_pos hl
    have hll := (Metric.tendsto_nhdsWithin_nhds.mp hl) ε hε
    rcases hll with ⟨δ₂, hδ₂_pos, hδ₂⟩
    refine ⟨min δ₁ δ₂, l, lt_min hδ₁_pos hδ₂_pos, hno, ?_, ?_⟩
    · intro u hu hdu
      simpa [Real.dist_eq] using hδ₁ hu (lt_of_lt_of_le hdu (min_le_left _ _))
    · intro u hu hdu
      simpa [Real.dist_eq] using hδ₂ hu (lt_of_lt_of_le hdu (min_le_right _ _))

private lemma cadlagSNL_mem_GoodN (p : CadlagSNL) (N : ℕ) : p.val ∈ GoodN N := by
  have hcomp : IsCompact (Icc (0 : NNReal) (N : NNReal)) := isCompact_Icc
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- RatBounded
    have hcov : ∀ t : NNReal, ∃ δ l, 0 < δ ∧ p.val t ≤ l ∧
        (∀ u : NNReal, t ≤ u → dist u t < δ → |p.val u - p.val t| < 1) ∧
        (∀ u : NNReal, u < t → dist u t < δ → |p.val u - l| < 1) :=
      fun t => cadlagSNL_local_ball p t zero_lt_one
    choose δ l hδ_pos _ hR hL using hcov
    have hsub : Icc (0 : NNReal) (N : NNReal) ⊆ ⋃ t : NNReal, Metric.ball t (δ t) :=
      fun t _ => mem_iUnion.mpr ⟨t, Metric.mem_ball_self (hδ_pos t)⟩
    rcases hcomp.elim_finite_subcover (fun t => Metric.ball t (δ t))
        (fun _ => Metric.isOpen_ball) hsub with ⟨S, hS⟩
    let B : ℝ := S.sup' (by
      rcases S.eq_empty_or_nonempty with hemp | hne
      · exfalso
        have h0 : (0 : NNReal) ∈ ⋃ i ∈ S, Metric.ball i (δ i) := hS ⟨le_rfl, bot_le⟩
        simp [hemp] at h0
      · exact hne) (fun t => max (|p.val t| + 1) (|l t| + 1))
    refine ⟨Nat.ceil B, fun q => ?_⟩
    have hq_mem : ratToNN q ∈ Icc (0 : NNReal) (N : NNReal) := ⟨bot_le, ratToNN_le q⟩
    rcases mem_iUnion₂.mp (hS hq_mem) with ⟨t, htS, hball⟩
    have hdist : dist (ratToNN q) t < δ t := Metric.mem_ball.mp hball
    have hBt : max (|p.val t| + 1) (|l t| + 1) ≤ B :=
      Finset.le_sup' (f := fun t => max (|p.val t| + 1) (|l t| + 1)) htS
    have hleB : |p.val (ratToNN q)| ≤ B := by
      rcases le_or_gt t (ratToNN q) with hle | hlt
      · have h1 := hR t (ratToNN q) hle hdist
        have h2 : |p.val (ratToNN q)| ≤ |p.val t| + 1 := by
          have := abs_sub_abs_le_abs_sub (p.val (ratToNN q)) (p.val t)
          linarith
        exact h2.trans ((le_max_left _ _).trans hBt)
      · have h1 := hL t (ratToNN q) hlt hdist
        have h2 : |p.val (ratToNN q)| ≤ |l t| + 1 := by
          have := abs_sub_abs_le_abs_sub (p.val (ratToNN q)) (l t)
          linarith
        exact h2.trans ((le_max_right _ _).trans hBt)
    exact hleB.trans (Nat.le_ceil B)
  · -- RatNoOsc (pigeonhole over left/right halves of finite cover)
    intro a b hab
    have hε : 0 < ((b : ℝ) - (a : ℝ)) / 3 := by
      have : (a : ℝ) < (b : ℝ) := Rat.cast_lt.mpr hab
      linarith
    have hcov : ∀ t : NNReal, ∃ δ l, 0 < δ ∧ p.val t ≤ l ∧
        (∀ u : NNReal, t ≤ u → dist u t < δ → |p.val u - p.val t| < ((b : ℝ) - (a : ℝ)) / 3) ∧
        (∀ u : NNReal, u < t → dist u t < δ → |p.val u - l| < ((b : ℝ) - (a : ℝ)) / 3) :=
      fun t => cadlagSNL_local_ball p t hε
    choose δ l hδ_pos _ hR hL using hcov
    have hsub : Icc (0 : NNReal) (N : NNReal) ⊆ ⋃ t : NNReal, Metric.ball t (δ t) :=
      fun t _ => mem_iUnion.mpr ⟨t, Metric.mem_ball_self (hδ_pos t)⟩
    rcases hcomp.elim_finite_subcover (fun t => Metric.ball t (δ t))
        (fun _ => Metric.isOpen_ball) hsub with ⟨S, hS⟩
    refine ⟨S.card, fun qs hmono hosc => ?_⟩
    -- Assign each i : Fin (2 * S.card + 1) to (t ∈ S, side ∈ Bool) where side=true iff t ≤ qs i
    have hassign : ∀ i : Fin (2 * S.card + 1),
        ∃ c : {t // t ∈ S} × Bool,
          dist (ratToNN (qs i)) c.1.1 < δ c.1.1 ∧
          (c.2 = true → c.1.1 ≤ ratToNN (qs i)) ∧
          (c.2 = false → ratToNN (qs i) < c.1.1) := by
      intro i
      have hmem : ratToNN (qs i) ∈ Icc (0 : NNReal) (N : NNReal) := ⟨bot_le, ratToNN_le (qs i)⟩
      rcases mem_iUnion₂.mp (hS hmem) with ⟨t, htS, hball⟩
      by_cases hle : t ≤ ratToNN (qs i)
      · exact ⟨(⟨t, htS⟩, true), Metric.mem_ball.mp hball, fun _ => hle, fun h => by simp at h⟩
      · exact ⟨(⟨t, htS⟩, false), Metric.mem_ball.mp hball, fun h => by simp at h, fun _ => lt_of_not_ge hle⟩
    choose col hcol_dist hcol_T hcol_F using hassign
    have hmono_nn : StrictMono (fun i => ratToNN (qs i)) := fun i j hij => by
      rw [← NNReal.coe_lt_coe, ratToNN_coe, ratToNN_coe]
      exact Rat.cast_lt.mpr (hmono hij)
    -- Two indices with same color cannot have opposite parity (nor can an intermediate index!)
    have hno_opp : ∀ i j : Fin (2 * S.card + 1), col i = col j →
        Even i.val → ¬ Even j.val → False := by
      intro i j hcij hi hj
      have hi_val : p.val (ratToNN (qs i)) ≤ (a : ℝ) := by simpa [hi] using hosc i
      have hj_val : (b : ℝ) ≤ p.val (ratToNN (qs j)) := by simpa [hj] using hosc j
      cases hside : (col i).2 with
      | true =>
        have h1 := hR (col i).1.1 (ratToNN (qs i)) (hcol_T i hside) (hcol_dist i)
        have hside_j : (col j).2 = true := hcij ▸ hside
        have h2 := hR (col i).1.1 (ratToNN (qs j))
          (by simpa [hcij] using hcol_T j hside_j) (by simpa [hcij] using hcol_dist j)
        have hdiff : |p.val (ratToNN (qs j)) - p.val (ratToNN (qs i))| <
            2 * (((b : ℝ) - (a : ℝ)) / 3) := by
          calc |p.val (ratToNN (qs j)) - p.val (ratToNN (qs i))|
              = |(p.val (ratToNN (qs j)) - p.val (col i).1.1) -
                  (p.val (ratToNN (qs i)) - p.val (col i).1.1)| := by ring_nf
            _ ≤ |p.val (ratToNN (qs j)) - p.val (col i).1.1| +
                |p.val (ratToNN (qs i)) - p.val (col i).1.1| := abs_sub _ _
            _ < ((b : ℝ) - (a : ℝ)) / 3 + ((b : ℝ) - (a : ℝ)) / 3 := add_lt_add h2 h1
            _ = 2 * (((b : ℝ) - (a : ℝ)) / 3) := by ring
        have hge : (b : ℝ) - (a : ℝ) ≤ p.val (ratToNN (qs j)) - p.val (ratToNN (qs i)) := by linarith
        linarith [(abs_lt.mp hdiff).2]
      | false =>
        have h1 := hL (col i).1.1 (ratToNN (qs i)) (hcol_F i hside) (hcol_dist i)
        have hside_j : (col j).2 = false := hcij ▸ hside
        have h2 := hL (col i).1.1 (ratToNN (qs j))
          (by simpa [hcij] using hcol_F j hside_j) (by simpa [hcij] using hcol_dist j)
        have hdiff : |p.val (ratToNN (qs j)) - p.val (ratToNN (qs i))| <
            2 * (((b : ℝ) - (a : ℝ)) / 3) := by
          calc |p.val (ratToNN (qs j)) - p.val (ratToNN (qs i))|
              = |(p.val (ratToNN (qs j)) - l (col i).1.1) -
                  (p.val (ratToNN (qs i)) - l (col i).1.1)| := by ring_nf
            _ ≤ |p.val (ratToNN (qs j)) - l (col i).1.1| +
                |p.val (ratToNN (qs i)) - l (col i).1.1| := abs_sub _ _
            _ < ((b : ℝ) - (a : ℝ)) / 3 + ((b : ℝ) - (a : ℝ)) / 3 := add_lt_add h2 h1
            _ = 2 * (((b : ℝ) - (a : ℝ)) / 3) := by ring
        have hge : (b : ℝ) - (a : ℝ) ≤ p.val (ratToNN (qs j)) - p.val (ratToNN (qs i)) := by linarith
        linarith [(abs_lt.mp hdiff).2]
    -- Show col is injective because each half is an interval (OrdConnected)
    have hno_lt : ∀ i j : Fin (2 * S.card + 1), i < j → col i = col j → False := by
      intro i j hij hcij
      have hk_lt : i.val + 1 < 2 * S.card + 1 := lt_of_le_of_lt (Nat.succ_le_of_lt hij) j.isLt
      let k : Fin (2 * S.card + 1) := ⟨i.val + 1, hk_lt⟩
      have hik : ratToNN (qs i) < ratToNN (qs k) := hmono_nn (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i.val))
      have hkj : ratToNN (qs k) ≤ ratToNN (qs j) := hmono_nn.monotone (Nat.succ_le_of_lt hij)
      -- Therefore ratToNN (qs k) ALSO lies in the same half as i and j!
      have hsame_k :
          dist (ratToNN (qs k)) (col i).1.1 < δ (col i).1.1 ∧
          ((col i).2 = true → (col i).1.1 ≤ ratToNN (qs k)) ∧
          ((col i).2 = false → ratToNN (qs k) < (col i).1.1) := by
        cases hside : (col i).2 with
        | true =>
          have hi_ge : (col i).1.1 ≤ ratToNN (qs i) := hcol_T i hside
          have hk_ge : (col i).1.1 ≤ ratToNN (qs k) := hi_ge.trans hik.le
          have hj_dist : dist (ratToNN (qs j)) (col i).1.1 < δ (col i).1.1 := by
            simpa [hcij] using hcol_dist j
          have hk_dist : dist (ratToNN (qs k)) (col i).1.1 < δ (col i).1.1 := by
            rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hk_ge))]
            rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hk_ge.trans hkj)))] at hj_dist
            linarith [NNReal.coe_le_coe.mpr hkj]
          exact ⟨hk_dist, fun _ => hk_ge, fun h => by simp at h⟩
        | false =>
          have hj_lt : ratToNN (qs j) < (col i).1.1 := by
            simpa [hcij] using hcol_F j (hcij ▸ hside)
          have hk_lt' : ratToNN (qs k) < (col i).1.1 := lt_of_le_of_lt hkj hj_lt
          have hi_dist : dist (ratToNN (qs i)) (col i).1.1 < δ (col i).1.1 := hcol_dist i
          have hk_dist : dist (ratToNN (qs k)) (col i).1.1 < δ (col i).1.1 := by
            rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hk_lt'.le))]
            rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr (hik.le.trans hk_lt'.le)))] at hi_dist
            linarith [NNReal.coe_lt_coe.mpr hik]
          exact ⟨hk_dist, fun h => by simp at h, fun _ => hk_lt'⟩
      -- Now i and k have opposite parity AND lie in the same half -> contradiction!
      have hopp : (Even i.val ∧ ¬ Even k.val) ∨ (Even k.val ∧ ¬ Even i.val) := by
        by_cases he : Even i.val
        · left; exact ⟨he, by simp [k, Nat.even_add_one, he]⟩
        · right; exact ⟨by simp [k, Nat.even_add_one, he], he⟩
      have hosc_ik : |p.val (ratToNN (qs k)) - p.val (ratToNN (qs i))| ≥ (b : ℝ) - (a : ℝ) := by
        rcases hopp with ⟨hiE, hkO⟩ | ⟨hkE, hiO⟩
        · have h1 : p.val (ratToNN (qs i)) ≤ (a : ℝ) := by simpa [hiE] using hosc i
          have h2 : (b : ℝ) ≤ p.val (ratToNN (qs k)) := by simpa [hkO] using hosc k
          rw [abs_of_nonneg (by linarith)]; linarith
        · have h1 : (b : ℝ) ≤ p.val (ratToNN (qs i)) := by simpa [hiO] using hosc i
          have h2 : p.val (ratToNN (qs k)) ≤ (a : ℝ) := by simpa [hkE] using hosc k
          rw [abs_of_nonpos (by linarith)]; linarith
      have hosc_lt : |p.val (ratToNN (qs k)) - p.val (ratToNN (qs i))| <
          2 * (((b : ℝ) - (a : ℝ)) / 3) := by
        cases hside : (col i).2 with
        | true =>
          have h1 := hR (col i).1.1 (ratToNN (qs i)) (hcol_T i hside) (hcol_dist i)
          have h2 := hR (col i).1.1 (ratToNN (qs k)) (hsame_k.2.1 hside) hsame_k.1
          calc |p.val (ratToNN (qs k)) - p.val (ratToNN (qs i))|
              = |(p.val (ratToNN (qs k)) - p.val (col i).1.1) -
                  (p.val (ratToNN (qs i)) - p.val (col i).1.1)| := by ring_nf
            _ ≤ |p.val (ratToNN (qs k)) - p.val (col i).1.1| +
                |p.val (ratToNN (qs i)) - p.val (col i).1.1| := abs_sub _ _
            _ < ((b : ℝ) - (a : ℝ)) / 3 + ((b : ℝ) - (a : ℝ)) / 3 := add_lt_add h2 h1
            _ = 2 * (((b : ℝ) - (a : ℝ)) / 3) := by ring
        | false =>
          have h1 := hL (col i).1.1 (ratToNN (qs i)) (hcol_F i hside) (hcol_dist i)
          have h2 := hL (col i).1.1 (ratToNN (qs k)) (hsame_k.2.2 hside) hsame_k.1
          calc |p.val (ratToNN (qs k)) - p.val (ratToNN (qs i))|
              = |(p.val (ratToNN (qs k)) - l (col i).1.1) -
                  (p.val (ratToNN (qs i)) - l (col i).1.1)| := by ring_nf
            _ ≤ |p.val (ratToNN (qs k)) - l (col i).1.1| +
                |p.val (ratToNN (qs i)) - l (col i).1.1| := abs_sub _ _
            _ < ((b : ℝ) - (a : ℝ)) / 3 + ((b : ℝ) - (a : ℝ)) / 3 := add_lt_add h2 h1
            _ = 2 * (((b : ℝ) - (a : ℝ)) / 3) := by ring
      linarith
    have hinj : Function.Injective col := by
      intro i j hcij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hij | hji
      · exact hno_lt i j hij hcij
      · exact hno_lt j i hji hcij.symm
    have hcard := Fintype.card_le_of_injective col hinj
    simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_coe, Fintype.card_bool] at hcard
    omega
  · -- RatNoPosJumps (via Lebesgue number lemma!)
    intro k
    have hε : 0 < 1 / (3 * ((k : ℝ) + 1)) := by positivity
    have hcov : ∀ t : NNReal, ∃ δ l, 0 < δ ∧ p.val t ≤ l ∧
        (∀ u : NNReal, t ≤ u → dist u t < δ → |p.val u - p.val t| < 1 / (3 * ((k : ℝ) + 1))) ∧
        (∀ u : NNReal, u < t → dist u t < δ → |p.val u - l| < 1 / (3 * ((k : ℝ) + 1))) :=
      fun t => cadlagSNL_local_ball p t hε
    choose δ l hδ_pos hno hR hL using hcov
    have hsub : Icc (0 : NNReal) (N : NNReal) ⊆ ⋃ t : NNReal, Metric.ball t (δ t) :=
      fun t _ => mem_iUnion.mpr ⟨t, Metric.mem_ball_self (hδ_pos t)⟩
    rcases lebesgue_number_lemma_of_metric hcomp (fun _ => Metric.isOpen_ball) hsub with
      ⟨ρ, hρ_pos, hρ⟩
    rcases exists_nat_gt (1 / ρ) with ⟨m, hm⟩
    refine ⟨m, fun q1 q2 hq12 hdiff => ?_⟩
    have hinv_lt : 1 / ((m : ℝ) + 1) < ρ := by
      have hm1 : 1 / ρ < (m : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ (by positivity)] at hm1 ⊢
      linarith
    have hmem1 : ratToNN q1 ∈ Icc (0 : NNReal) (N : NNReal) := ⟨bot_le, ratToNN_le q1⟩
    rcases hρ (ratToNN q1) hmem1 with ⟨t, ht⟩
    have hd1 : dist (ratToNN q1) t < δ t := Metric.mem_ball.mp (ht (Metric.mem_ball_self hρ_pos))
    have hd12 : dist (ratToNN q2) (ratToNN q1) < ρ := by
      rw [NNReal.dist_eq, ratToNN_coe, ratToNN_coe,
        abs_of_nonneg (sub_nonneg.mpr (Rat.cast_le.mpr hq12.le))]
      exact hdiff.trans hinv_lt
    have hd2 : dist (ratToNN q2) t < δ t := Metric.mem_ball.mp (ht (Metric.mem_ball.mpr hd12))
    have hq12_nn : ratToNN q1 < ratToNN q2 := by
      rw [← NNReal.coe_lt_coe, ratToNN_coe, ratToNN_coe]
      exact Rat.cast_lt.mpr hq12
    have h23 : 1 / (3 * ((k : ℝ) + 1)) + 1 / (3 * ((k : ℝ) + 1)) < 1 / ((k : ℝ) + 1) := by
      have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h3 : (2 : ℝ) / (3 * ((k : ℝ) + 1)) < 1 / ((k : ℝ) + 1) := by
        rw [div_lt_div_iff₀ (by positivity) hk_pos]
        linarith
      have hsum : 1 / (3 * ((k : ℝ) + 1)) + 1 / (3 * ((k : ℝ) + 1)) = 2 / (3 * ((k : ℝ) + 1)) := by ring
      linarith
    by_cases h1 : t ≤ ratToNN q1
    · have h2 : t ≤ ratToNN q2 := h1.trans hq12_nn.le
      have ha := hR t (ratToNN q1) h1 hd1
      have hb := hR t (ratToNN q2) h2 hd2
      have := (abs_lt.mp ha).1; have := (abs_lt.mp hb).2
      linarith
    · have h1lt : ratToNN q1 < t := lt_of_not_ge h1
      have ha := hL t (ratToNN q1) h1lt hd1
      by_cases h2 : t ≤ ratToNN q2
      · have hb := hR t (ratToNN q2) h2 hd2
        have := (abs_lt.mp ha).1; have := (abs_lt.mp hb).2; have := hno t
        linarith
      · have h2lt : ratToNN q2 < t := lt_of_not_ge h2
        have hb := hL t (ratToNN q2) h2lt hd2
        have := (abs_lt.mp ha).1; have := (abs_lt.mp hb).2
        linarith
  · -- RatZeroRightCont
    intro k
    have hε : 0 < 1 / ((k : ℝ) + 1) := by positivity
    rcases Metric.continuousWithinAt_iff.mp (p.rightCont 0) (1 / ((k : ℝ) + 1)) hε with
      ⟨δ, hδ_pos, hδ⟩
    rcases exists_nat_gt (1 / δ) with ⟨m, hm⟩
    refine ⟨m, fun q hq => ?_⟩
    have hinv_lt : 1 / ((m : ℝ) + 1) < δ := by
      have hm1 : 1 / δ < (m : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ (by positivity)] at hm1 ⊢
      linarith
    have hdist : dist (ratToNN q) (0 : NNReal) < δ := by
      rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, ratToNN_coe,
        abs_of_nonneg (Rat.cast_nonneg.mpr q.2.1)]
      exact hq.trans hinv_lt
    have hX := hδ (Set.mem_Ici.mpr bot_le) hdist
    rw [Real.dist_eq, p.val_zero, sub_zero] at hX
    exact hX.le

/-! ### 4. Reconstructing a `CadlagSNL` path from `f ∈ Good` via rational right limits -/

private noncomputable def ratAbove (t : NNReal) (k : ℕ) : NNReal :=
  ((Nat.floor ((t : ℝ) * ((k : ℝ) + 1)) + 1 : ℕ) : NNReal) / ((k : NNReal) + 1)

private lemma ratAbove_gt (t : NNReal) (k : ℕ) : t < ratAbove t k := by
  rw [← NNReal.coe_lt_coe]
  dsimp only [ratAbove]
  push_cast
  rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
  exact Nat.lt_floor_add_one ((t : ℝ) * ((k : ℝ) + 1))

private lemma ratAbove_le (t : NNReal) (k : ℕ) :
    (ratAbove t k : ℝ) ≤ (t : ℝ) + 1 / ((k : ℝ) + 1) := by
  dsimp only [ratAbove]
  push_cast
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
  have hfl : (Nat.floor ((t : ℝ) * ((k : ℝ) + 1)) : ℝ) ≤ (t : ℝ) * ((k : ℝ) + 1) :=
    Nat.floor_le (by positivity)
  have h1 : ((t : ℝ) + 1 / ((k : ℝ) + 1)) * ((k : ℝ) + 1) = (t : ℝ) * ((k : ℝ) + 1) + 1 := by
    field_simp
  linarith

private lemma ratAbove_isRat (t : NNReal) (k : ℕ) :
    ∃ q : ℚ, 0 ≤ q ∧ Real.toNNReal (q : ℝ) = ratAbove t k := by
  let q : ℚ := ((Nat.floor ((t : ℝ) * ((k : ℝ) + 1)) + 1 : ℕ) : ℚ) / ((k : ℚ) + 1)
  refine ⟨q, by positivity, ?_⟩
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal (q : ℝ) (by positivity)]
  dsimp only [q, ratAbove]
  push_cast
  rfl

private lemma ratAbove_tendsto (t : NNReal) :
    Tendsto (ratAbove t) atTop (𝓝[Ici t] t) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall fun k => (ratAbove_gt t k).le⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases exists_nat_gt (1 / ε) with ⟨K, hK⟩
  refine ⟨K, fun k hk => ?_⟩
  rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ratAbove_gt t k).le))]
  have hle := ratAbove_le t k
  have hk' : 1 / ε < (k : ℝ) + 1 := by
    have : (K : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    linarith
  have hinv : 1 / ((k : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ (by positivity)] at hk' ⊢
    linarith
  linarith

private lemma exists_rat_rightLim {N : ℕ} {f : NNReal → ℝ}
    (hb : RatBounded N f) (hosc : RatNoOsc N f) {t : NNReal} (ht : (t : ℝ) < (N : ℝ)) :
    ∃ y : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ q : RatDom N,
      t < ratToNN q → (ratToNN q : ℝ) < (t : ℝ) + δ → |f (ratToNN q) - y| < ε := by
  -- Use liminf/limsup along the filter ℱ = comap ratToNN (𝓝[>] t)
  let ℱ : Filter (RatDom N) := Filter.comap (fun q : RatDom N => ratToNN q) (𝓝[>] t)
  have hNe : ℱ.NeBot := by
    rw [Filter.comap_neBot_iff]
    intro s hs
    rw [Metric.mem_nhdsWithin_iff] at hs
    rcases hs with ⟨δ, hδ_pos, hδ⟩
    let hi : ℝ := min (N : ℝ) ((t : ℝ) + δ)
    have hthi : (t : ℝ) < hi := lt_min ht (by linarith)
    rcases exists_rat_btwn hthi with ⟨q, htq, hqhi⟩
    have hq_nn : 0 ≤ q := Rat.cast_nonneg.mp ((NNReal.coe_nonneg t).trans htq.le)
    have hq_le : q ≤ (N : ℚ) := by
      have : (q : ℝ) ≤ (N : ℝ) := hqhi.le.trans (min_le_left _ _)
      exact_mod_cast this
    let qd : RatDom N := ⟨q, hq_nn, hq_le⟩
    refine ⟨qd, hδ ⟨?_, ?_⟩⟩
    · rw [Metric.mem_ball, NNReal.dist_eq, ratToNN_coe, abs_of_nonneg (sub_nonneg.mpr htq.le)]
      linarith [lt_of_lt_of_le hqhi (min_le_right _ _)]
    · change t < ratToNN qd
      rw [← NNReal.coe_lt_coe, ratToNN_coe]
      exact htq
  rcases hb with ⟨M, hM⟩
  have hBddAbove : Filter.IsBoundedUnder (· ≤ ·) ℱ (fun q : RatDom N => f (ratToNN q)) :=
    ⟨(M : ℝ), Filter.eventually_map.mpr (Eventually.of_forall fun q => (le_abs_self _).trans (hM q))⟩
  have hBddBelow : Filter.IsBoundedUnder (· ≥ ·) ℱ (fun q : RatDom N => f (ratToNN q)) :=
    ⟨-(M : ℝ), Filter.eventually_map.mpr (Eventually.of_forall fun q => by linarith [(abs_le.mp (hM q)).1])⟩
  let li := Filter.liminf (fun q : RatDom N => f (ratToNN q)) ℱ
  let ls := Filter.limsup (fun q : RatDom N => f (ratToNN q)) ℱ
  have hli_le : li ≤ ls := Filter.liminf_le_limsup hBddAbove hBddBelow
  have heq : li = ls := by
    by_contra hne
    have hlt : li < ls := lt_of_le_of_ne hli_le hne
    rcases exists_rat_btwn hlt with ⟨a, hlia, hals⟩
    rcases exists_rat_btwn hals with ⟨b, hab, hbls⟩
    have hfreqA : ∃ᶠ q in ℱ, f (ratToNN q) < (a : ℝ) :=
      Filter.frequently_lt_of_liminf_lt (hBddAbove.isCoboundedUnder_ge) hlia
    have hfreqB : ∃ᶠ q in ℱ, (b : ℝ) < f (ratToNN q) :=
      Filter.frequently_lt_of_lt_limsup (hBddBelow.isCoboundedUnder_le) hbls
    -- Helper: in any (t, u), find q with f q < a (resp. b < f q)
    have hpickA : ∀ u : ℝ, (t : ℝ) < u → ∃ q : RatDom N, t < ratToNN q ∧ (ratToNN q : ℝ) < u ∧ f (ratToNN q) ≤ (a : ℝ) := by
      intro u hu
      have hmem : {q : RatDom N | (ratToNN q : ℝ) < u ∧ t < ratToNN q} ∈ ℱ := by
        refine ⟨Ioi t ∩ Metric.ball t (u - (t : ℝ)), ?_, fun q hq => ?_⟩
        · exact inter_mem_nhdsWithin (Ioi t) (Metric.ball_mem_nhds t (sub_pos.mpr hu))
        · rcases hq with ⟨hgt, hbq⟩
          have hdist : |(ratToNN q : ℝ) - (t : ℝ)| < u - (t : ℝ) := by
            simpa [Metric.mem_ball, NNReal.dist_eq] using hbq
          exact ⟨by linarith [(abs_lt.mp hdist).2], hgt⟩
      rcases (hfreqA.and_eventually hmem).exists with ⟨q, hfa, hqu, hqt⟩
      exact ⟨q, hqt, hqu, hfa.le⟩
    have hpickB : ∀ u : ℝ, (t : ℝ) < u → ∃ q : RatDom N, t < ratToNN q ∧ (ratToNN q : ℝ) < u ∧ (b : ℝ) ≤ f (ratToNN q) := by
      intro u hu
      have hmem : {q : RatDom N | (ratToNN q : ℝ) < u ∧ t < ratToNN q} ∈ ℱ := by
        refine ⟨Ioi t ∩ Metric.ball t (u - (t : ℝ)), ?_, fun q hq => ?_⟩
        · exact inter_mem_nhdsWithin (Ioi t) (Metric.ball_mem_nhds t (sub_pos.mpr hu))
        · rcases hq with ⟨hgt, hbq⟩
          have hdist : |(ratToNN q : ℝ) - (t : ℝ)| < u - (t : ℝ) := by
            simpa [Metric.mem_ball, NNReal.dist_eq] using hbq
          exact ⟨by linarith [(abs_lt.mp hdist).2], hgt⟩
      rcases (hfreqB.and_eventually hmem).exists with ⟨q, hfb, hqu, hqt⟩
      exact ⟨q, hqt, hqu, hfb.le⟩
    rcases hosc a b (Rat.cast_lt.mp hab) with ⟨m, hm⟩
    have hchain : ∀ n : ℕ, ∃ r : Fin (n + 1) → RatDom N,
        (∀ i : Fin (n + 1), t < ratToNN (r i)) ∧
        (∀ i : Fin n, (r i.succ).1 < (r i.castSucc).1) ∧
        (∀ i : Fin (n + 1), if Even i.val then f (ratToNN (r i)) ≤ (a : ℝ) else (b : ℝ) ≤ f (ratToNN (r i))) := by
      intro n
      induction n with
      | zero =>
        rcases hpickA (N : ℝ) ht with ⟨q0, hq0t, _, hq0a⟩
        refine ⟨fun _ => q0, fun _ => hq0t, fun i => Fin.elim0 i, fun i => ?_⟩
        have hi0 : i.val = 0 := by omega
        rw [hi0]; simp [hq0a]
      | succ n ih =>
        rcases ih with ⟨r, hr_gt, hr_dec, hr_osc⟩
        let last := r (Fin.last n)
        have hlast_gt : (t : ℝ) < (ratToNN last : ℝ) := NNReal.coe_lt_coe.mpr (hr_gt (Fin.last n))
        have hnext : ∃ q : RatDom N, t < ratToNN q ∧ (ratToNN q : ℝ) < (ratToNN last : ℝ) ∧
            (if Even (n + 1) then f (ratToNN q) ≤ (a : ℝ) else (b : ℝ) ≤ f (ratToNN q)) := by
          by_cases he : Even (n + 1)
          · rcases hpickA (ratToNN last : ℝ) hlast_gt with ⟨q, h1, h2, h3⟩
            exact ⟨q, h1, h2, by simp [he, h3]⟩
          · rcases hpickB (ratToNN last : ℝ) hlast_gt with ⟨q, h1, h2, h3⟩
            exact ⟨q, h1, h2, by simp [he, h3]⟩
        rcases hnext with ⟨qn, hqn_gt, hqn_lt, hqn_osc⟩
        refine ⟨Fin.snoc r qn, ?_, ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · simpa using hqn_gt
          · intro j; simpa using hr_gt j
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
            have : (qn.1 : ℝ) < (last.1 : ℝ) := by
              rw [← ratToNN_coe, ← ratToNN_coe]; exact hqn_lt
            exact Rat.cast_lt.mp this
          · intro j
            simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
            exact hr_dec j
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · simpa using hqn_osc
          · intro j; simpa using hr_osc j
    rcases hchain (2 * m) with ⟨r, _, hr_dec, hr_osc⟩
    let qs : Fin (2 * m + 1) → RatDom N := fun i => r i.rev
    have hqs_mono : StrictMono (fun i => (qs i).1) := by
      have hanti : StrictAnti (fun i => (r i).1) := by
        intro i j hij
        have hstep : ∀ d (a : Fin (2 * m + 1)) (h : a.val + d + 1 < 2 * m + 1),
            (r ⟨a.val + d + 1, h⟩).1 < (r a).1 := by
          intro d
          induction d with
          | zero =>
            intro a h
            exact hr_dec ⟨a.val, by omega⟩
          | succ d ih =>
            intro a h
            have hprev : a.val + d + 1 < 2 * m + 1 := by omega
            have h1 : (r ⟨a.val + d + 1 + 1, h⟩).1 < (r ⟨a.val + d + 1, hprev⟩).1 :=
              hr_dec ⟨a.val + d + 1, by omega⟩
            exact h1.trans (ih a hprev)
        have hd : i.val + (j.val - i.val - 1) + 1 = j.val := by omega
        have hltj : i.val + (j.val - i.val - 1) + 1 < 2 * m + 1 := by omega
        have := hstep (j.val - i.val - 1) i hltj
        have heq_j : (⟨i.val + (j.val - i.val - 1) + 1, hltj⟩ : Fin (2 * m + 1)) = j :=
          Fin.ext hd
        rwa [heq_j] at this
      intro i j hij
      exact hanti (Fin.rev_lt_rev.mpr hij)
    have hqs_osc : ∀ i : Fin (2 * m + 1),
        if Even i.val then f (ratToNN (qs i)) ≤ (a : ℝ) else (b : ℝ) ≤ f (ratToNN (qs i)) := by
      intro i
      have hpar : Even i.rev.val ↔ Even i.val := by
        have hval : i.rev.val = 2 * m - i.val := by simp [Fin.rev]
        have hi_le : i.val ≤ 2 * m := by omega
        rw [hval, Nat.even_sub hi_le]
        simp
      have hro := hr_osc i.rev
      by_cases he : Even i.val
      · have hrev : Even i.rev.val := hpar.mpr he
        simp only [if_pos hrev] at hro
        simp only [qs, if_pos he]
        exact hro
      · have hrev : ¬Even i.rev.val := fun h => he (hpar.mp h)
        simp only [if_neg hrev] at hro
        simp only [qs, if_neg he]
        exact hro
    exact hm qs hqs_mono hqs_osc
  have htend : Tendsto (fun q : RatDom N => f (ratToNN q)) ℱ (𝓝 ls) :=
    tendsto_of_liminf_eq_limsup heq rfl hBddAbove hBddBelow
  refine ⟨ls, fun ε hε => ?_⟩
  have hmem : {q : RatDom N | |f (ratToNN q) - ls| < ε} ∈ ℱ := by
    have h1 := htend (Metric.ball_mem_nhds ls hε)
    rw [Filter.mem_map] at h1
    refine Filter.mem_of_superset h1 fun q hq => ?_
    simpa [Metric.mem_ball, Real.dist_eq] using hq
  rcases hmem with ⟨U, hU, hUsub⟩
  rcases Metric.mem_nhdsWithin_iff.mp hU with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun q hqt hqδ => ?_⟩
  have hqU : ratToNN q ∈ U := hδ ⟨by
    rw [Metric.mem_ball, NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hqt.le))]
    linarith, hqt⟩
  exact hUsub hqU

private lemma exists_rat_leftLim {N : ℕ} {f : NNReal → ℝ}
    (hb : RatBounded N f) (hosc : RatNoOsc N f) {t : NNReal} (ht_pos : 0 < t) (ht_le : (t : ℝ) ≤ (N : ℝ)) :
    ∃ l : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ q : RatDom N,
      ratToNN q < t → (t : ℝ) - δ < (ratToNN q : ℝ) → |f (ratToNN q) - l| < ε := by
  let ℱ : Filter (RatDom N) := Filter.comap (fun q : RatDom N => ratToNN q) (𝓝[<] t)
  have hNe : ℱ.NeBot := by
    rw [Filter.comap_neBot_iff]
    intro s hs
    rw [Metric.mem_nhdsWithin_iff] at hs
    rcases hs with ⟨δ, hδ_pos, hδ⟩
    let lo : ℝ := max 0 ((t : ℝ) - δ)
    have hlot : lo < (t : ℝ) := max_lt (NNReal.coe_pos.mpr ht_pos) (by linarith)
    rcases exists_rat_btwn hlot with ⟨q, hloq, hqt⟩
    have hq_nn : 0 ≤ q := Rat.cast_nonneg.mp ((le_max_left _ _).trans hloq.le)
    have hq_le : q ≤ (N : ℚ) := by
      have : (q : ℝ) ≤ (N : ℝ) := hqt.le.trans ht_le
      exact_mod_cast this
    let qd : RatDom N := ⟨q, hq_nn, hq_le⟩
    refine ⟨qd, hδ ⟨?_, ?_⟩⟩
    · rw [Metric.mem_ball, NNReal.dist_eq, ratToNN_coe, abs_of_nonpos (sub_nonpos.mpr hqt.le)]
      linarith [lt_of_le_of_lt (le_max_right 0 ((t : ℝ) - δ)) hloq]
    · change ratToNN qd < t
      rw [← NNReal.coe_lt_coe, ratToNN_coe]
      exact hqt
  rcases hb with ⟨M, hM⟩
  have hBddAbove : Filter.IsBoundedUnder (· ≤ ·) ℱ (fun q : RatDom N => f (ratToNN q)) :=
    ⟨(M : ℝ), Filter.eventually_map.mpr (Eventually.of_forall fun q => (le_abs_self _).trans (hM q))⟩
  have hBddBelow : Filter.IsBoundedUnder (· ≥ ·) ℱ (fun q : RatDom N => f (ratToNN q)) :=
    ⟨-(M : ℝ), Filter.eventually_map.mpr (Eventually.of_forall fun q => by linarith [(abs_le.mp (hM q)).1])⟩
  let li := Filter.liminf (fun q : RatDom N => f (ratToNN q)) ℱ
  let ls := Filter.limsup (fun q : RatDom N => f (ratToNN q)) ℱ
  have hli_le : li ≤ ls := Filter.liminf_le_limsup hBddAbove hBddBelow
  have heq : li = ls := by
    by_contra hne
    have hlt : li < ls := lt_of_le_of_ne hli_le hne
    rcases exists_rat_btwn hlt with ⟨a, hlia, hals⟩
    rcases exists_rat_btwn hals with ⟨b, hab, hbls⟩
    have hfreqA : ∃ᶠ q in ℱ, f (ratToNN q) < (a : ℝ) :=
      Filter.frequently_lt_of_liminf_lt (hBddAbove.isCoboundedUnder_ge) hlia
    have hfreqB : ∃ᶠ q in ℱ, (b : ℝ) < f (ratToNN q) :=
      Filter.frequently_lt_of_lt_limsup (hBddBelow.isCoboundedUnder_le) hbls
    have hpickA : ∀ u : ℝ, u < (t : ℝ) → ∃ q : RatDom N, u < (ratToNN q : ℝ) ∧ ratToNN q < t ∧ f (ratToNN q) ≤ (a : ℝ) := by
      intro u hu
      have hmem : {q : RatDom N | u < (ratToNN q : ℝ) ∧ ratToNN q < t} ∈ ℱ := by
        refine ⟨Iio t ∩ Metric.ball t ((t : ℝ) - u), ?_, fun q hq => ?_⟩
        · exact inter_mem_nhdsWithin (Iio t) (Metric.ball_mem_nhds t (sub_pos.mpr hu))
        · rcases hq with ⟨hltq, hbq⟩
          have hdist : |(ratToNN q : ℝ) - (t : ℝ)| < (t : ℝ) - u := by
            simpa [Metric.mem_ball, NNReal.dist_eq] using hbq
          exact ⟨by linarith [(abs_lt.mp hdist).1], hltq⟩
      rcases (hfreqA.and_eventually hmem).exists with ⟨q, hfa, hqu, hqt⟩
      exact ⟨q, hqu, hqt, hfa.le⟩
    have hpickB : ∀ u : ℝ, u < (t : ℝ) → ∃ q : RatDom N, u < (ratToNN q : ℝ) ∧ ratToNN q < t ∧ (b : ℝ) ≤ f (ratToNN q) := by
      intro u hu
      have hmem : {q : RatDom N | u < (ratToNN q : ℝ) ∧ ratToNN q < t} ∈ ℱ := by
        refine ⟨Iio t ∩ Metric.ball t ((t : ℝ) - u), ?_, fun q hq => ?_⟩
        · exact inter_mem_nhdsWithin (Iio t) (Metric.ball_mem_nhds t (sub_pos.mpr hu))
        · rcases hq with ⟨hltq, hbq⟩
          have hdist : |(ratToNN q : ℝ) - (t : ℝ)| < (t : ℝ) - u := by
            simpa [Metric.mem_ball, NNReal.dist_eq] using hbq
          exact ⟨by linarith [(abs_lt.mp hdist).1], hltq⟩
      rcases (hfreqB.and_eventually hmem).exists with ⟨q, hfb, hqu, hqt⟩
      exact ⟨q, hqu, hqt, hfb.le⟩
    rcases hosc a b (Rat.cast_lt.mp hab) with ⟨m, hm⟩
    have hchain : ∀ n : ℕ, ∃ r : Fin (n + 1) → RatDom N,
        (∀ i : Fin (n + 1), ratToNN (r i) < t) ∧
        (∀ i : Fin n, (r i.castSucc).1 < (r i.succ).1) ∧
        (∀ i : Fin (n + 1), if Even i.val then f (ratToNN (r i)) ≤ (a : ℝ) else (b : ℝ) ≤ f (ratToNN (r i))) := by
      intro n
      induction n with
      | zero =>
        rcases hpickA 0 (NNReal.coe_pos.mpr ht_pos) with ⟨q0, _, hq0t, hq0a⟩
        refine ⟨fun _ => q0, fun _ => hq0t, fun i => Fin.elim0 i, fun i => ?_⟩
        have hi0 : i.val = 0 := by omega
        rw [hi0]; simp [hq0a]
      | succ n ih =>
        rcases ih with ⟨r, hr_lt, hr_inc, hr_osc⟩
        let last := r (Fin.last n)
        have hlast_lt : (ratToNN last : ℝ) < (t : ℝ) := NNReal.coe_lt_coe.mpr (hr_lt (Fin.last n))
        have hnext : ∃ q : RatDom N, (ratToNN last : ℝ) < (ratToNN q : ℝ) ∧ ratToNN q < t ∧
            (if Even (n + 1) then f (ratToNN q) ≤ (a : ℝ) else (b : ℝ) ≤ f (ratToNN q)) := by
          by_cases he : Even (n + 1)
          · rcases hpickA (ratToNN last : ℝ) hlast_lt with ⟨q, h1, h2, h3⟩
            exact ⟨q, h1, h2, by simp [he, h3]⟩
          · rcases hpickB (ratToNN last : ℝ) hlast_lt with ⟨q, h1, h2, h3⟩
            exact ⟨q, h1, h2, by simp [he, h3]⟩
        rcases hnext with ⟨qn, hqn_gt, hqn_lt, hqn_osc⟩
        refine ⟨Fin.snoc r qn, ?_, ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · simpa using hqn_lt
          · intro j; simpa using hr_lt j
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
            have : (last.1 : ℝ) < (qn.1 : ℝ) := by
              rw [← ratToNN_coe, ← ratToNN_coe]; exact hqn_gt
            exact Rat.cast_lt.mp this
          · intro j
            simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
            exact hr_inc j
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · simpa using hqn_osc
          · intro j; simpa using hr_osc j
    rcases hchain (2 * m) with ⟨r, _, hr_inc, hr_osc⟩
    have hr_mono : StrictMono (fun i => (r i).1) := by
      intro i j hij
      have hstep : ∀ d (a : Fin (2 * m + 1)) (h : a.val + d + 1 < 2 * m + 1),
          (r a).1 < (r ⟨a.val + d + 1, h⟩).1 := by
        intro d
        induction d with
        | zero =>
          intro a h
          exact hr_inc ⟨a.val, by omega⟩
        | succ d ih =>
          intro a h
          have hprev : a.val + d + 1 < 2 * m + 1 := by omega
          have h1 : (r ⟨a.val + d + 1, hprev⟩).1 < (r ⟨a.val + d + 1 + 1, h⟩).1 :=
            hr_inc ⟨a.val + d + 1, by omega⟩
          exact (ih a hprev).trans h1
      have hd : i.val + (j.val - i.val - 1) + 1 = j.val := by omega
      have hltj : i.val + (j.val - i.val - 1) + 1 < 2 * m + 1 := by omega
      have := hstep (j.val - i.val - 1) i hltj
      have heq_j : (⟨i.val + (j.val - i.val - 1) + 1, hltj⟩ : Fin (2 * m + 1)) = j :=
        Fin.ext hd
      rwa [heq_j] at this
    exact hm r hr_mono hr_osc
  have htend : Tendsto (fun q : RatDom N => f (ratToNN q)) ℱ (𝓝 ls) :=
    tendsto_of_liminf_eq_limsup heq rfl hBddAbove hBddBelow
  refine ⟨ls, fun ε hε => ?_⟩
  have hmem : {q : RatDom N | |f (ratToNN q) - ls| < ε} ∈ ℱ := by
    have h1 := htend (Metric.ball_mem_nhds ls hε)
    rw [Filter.mem_map] at h1
    refine Filter.mem_of_superset h1 fun q hq => ?_
    simpa [Metric.mem_ball, Real.dist_eq] using hq
  rcases hmem with ⟨U, hU, hUsub⟩
  rcases Metric.mem_nhdsWithin_iff.mp hU with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun q hqt hqδ => ?_⟩
  have hqU : ratToNN q ∈ U := hδ ⟨by
    rw [Metric.mem_ball, NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hqt.le))]
    linarith, hqt⟩
  exact hUsub hqU

private noncomputable def rightLimVal (f : NNReal → ℝ) (t : NNReal) : ℝ :=
  EReal.toReal (Filter.limsup (fun k : ℕ => ((f (ratAbove t k) : ℝ) : EReal)) atTop)

private lemma measurable_rightLimVal (t : NNReal) :
    Measurable (fun f : NNReal → ℝ => rightLimVal f t) := by
  have hm : ∀ k : ℕ, Measurable (fun f : NNReal → ℝ => ((f (ratAbove t k) : ℝ) : EReal)) :=
    fun k => measurable_coe_real_ereal.comp (measurable_pi_apply (ratAbove t k))
  exact measurable_ereal_toReal.comp (Measurable.limsup hm)

private lemma rightLimVal_eq_of_tendsto {f : NNReal → ℝ} {t : NNReal} {y : ℝ}
    (ht : Tendsto (fun k : ℕ => f (ratAbove t k)) atTop (𝓝 y)) :
    rightLimVal f t = y := by
  have hE : Tendsto (fun k : ℕ => ((f (ratAbove t k) : ℝ) : EReal)) atTop (𝓝 (y : EReal)) :=
    (continuous_coe_real_ereal.tendsto y).comp ht
  dsimp only [rightLimVal]
  rw [hE.limsup_eq, EReal.toReal_coe]

private lemma rightLimVal_eq_ratRightLim {f : NNReal → ℝ} {N : ℕ} {t : NNReal} {y : ℝ}
    (ht : (t : ℝ) < (N : ℝ))
    (hy : ∀ ε > 0, ∃ δ > 0, ∀ q : RatDom N,
      t < ratToNN q → (ratToNN q : ℝ) < (t : ℝ) + δ → |f (ratToNN q) - y| < ε) :
    rightLimVal f t = y := by
  refine rightLimVal_eq_of_tendsto ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases hy ε hε with ⟨δ, hδ_pos, hδ⟩
  rcases exists_nat_gt (1 / min δ ((N : ℝ) - (t : ℝ))) with ⟨K, hK⟩
  refine ⟨K, fun k hk => ?_⟩
  have hmin_pos : 0 < min δ ((N : ℝ) - (t : ℝ)) := lt_min hδ_pos (sub_pos.mpr ht)
  have hinv_lt : 1 / ((k : ℝ) + 1) < min δ ((N : ℝ) - (t : ℝ)) := by
    have hk' : 1 / min δ ((N : ℝ) - (t : ℝ)) < (k : ℝ) + 1 := by
      have : (K : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
      linarith
    rw [div_lt_iff₀ hmin_pos] at hk'
    rw [div_lt_iff₀ (by positivity)]
    linarith
  rcases ratAbove_isRat t k with ⟨q, hq_nn, hq_eq⟩
  have hq_le_N : q ≤ (N : ℚ) := by
    have h1 : (q : ℝ) = (ratAbove t k : ℝ) := by
      rw [← hq_eq, Real.coe_toNNReal (q : ℝ) (Rat.cast_nonneg.mpr hq_nn)]
    have h2 : (ratAbove t k : ℝ) ≤ (t : ℝ) + 1 / ((k : ℝ) + 1) := ratAbove_le t k
    have h3 : 1 / ((k : ℝ) + 1) < (N : ℝ) - (t : ℝ) := hinv_lt.trans_le (min_le_right _ _)
    have h4 : (q : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast h4
  let qd : RatDom N := ⟨q, hq_nn, hq_le_N⟩
  have hqd_eq : ratToNN qd = ratAbove t k := hq_eq
  rw [Real.dist_eq, ← hqd_eq]
  refine hδ qd (hqd_eq ▸ ratAbove_gt t k) ?_
  rw [hqd_eq]
  have h2 := ratAbove_le t k
  have h3 : 1 / ((k : ℝ) + 1) < δ := hinv_lt.trans_le (min_le_left _ _)
  linarith

private noncomputable def cadlagOfGood (f : NNReal → ℝ) (hf : f ∈ Good) : CadlagSNL := by
  have hgoodN : ∀ N : ℕ, f ∈ GoodN (N + 1) := fun N => mem_iInter.mp hf N
  have hright : ∀ t : NNReal, ∀ N : ℕ, (t : ℝ) < ((N + 1 : ℕ) : ℝ) →
      ∀ ε > 0, ∃ δ > 0, ∀ q : RatDom (N + 1),
        t < ratToNN q → (ratToNN q : ℝ) < (t : ℝ) + δ → |f (ratToNN q) - rightLimVal f t| < ε := by
    intro t N htN
    rcases exists_rat_rightLim (hgoodN N).1 (hgoodN N).2.1 htN with ⟨y, hy⟩
    have hyeq : rightLimVal f t = y := rightLimVal_eq_ratRightLim htN hy
    rwa [hyeq]
  have hleft : ∀ t : NNReal, 0 < t → ∀ N : ℕ, (t : ℝ) ≤ ((N + 1 : ℕ) : ℝ) →
      ∃ l : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ q : RatDom (N + 1),
        ratToNN q < t → (t : ℝ) - δ < (ratToNN q : ℝ) → |f (ratToNN q) - l| < ε :=
    fun t ht N htN => exists_rat_leftLim (hgoodN N).1 (hgoodN N).2.1 ht htN
  refine ⟨rightLimVal f, ?_, ?_, ?_, ?_⟩
  · -- val_zero
    have hrc0 := (hgoodN 0).2.2.2
    refine rightLimVal_eq_of_tendsto ?_
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases exists_nat_gt (1 / ε) with ⟨k, hk⟩
    rcases hrc0 k with ⟨m, hm⟩
    refine ⟨m + 1, fun j hj => ?_⟩
    rcases ratAbove_isRat 0 j with ⟨q, hq_nn, hq_eq⟩
    have hle1 : (ratAbove 0 j : ℝ) ≤ 1 / ((j : ℝ) + 1) := by
      simpa using ratAbove_le 0 j
    have hq_coe : (q : ℝ) = (ratAbove 0 j : ℝ) := by
      rw [← hq_eq, Real.coe_toNNReal (q : ℝ) (Rat.cast_nonneg.mpr hq_nn)]
    have hq_le1 : q ≤ ((0 + 1 : ℕ) : ℚ) := by
      have h1 : (q : ℝ) ≤ 1 := by
        rw [hq_coe]
        exact hle1.trans (div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) j]) (by positivity))
      exact_mod_cast h1
    let qd : RatDom (0 + 1) := ⟨q, hq_nn, hq_le1⟩
    have hqd_eq : ratToNN qd = ratAbove 0 j := hq_eq
    have hq_lt : (qd.1 : ℝ) < 1 / ((m : ℝ) + 1) := by
      change (q : ℝ) < 1 / ((m : ℝ) + 1)
      rw [hq_coe]
      have hj_gt : (m : ℝ) + 1 < (j : ℝ) + 1 := by
        have : (m : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj
        linarith
      have hdiv : 1 / ((j : ℝ) + 1) < 1 / ((m : ℝ) + 1) :=
        one_div_lt_one_div_of_lt (by positivity) hj_gt
      exact hle1.trans_lt hdiv
    have hbound := hm qd hq_lt
    rw [hqd_eq] at hbound
    have hk_inv : 1 / ((k : ℝ) + 1) < ε := by
      have hk1 : 1 / ε < (k : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hε] at hk1
      rw [div_lt_iff₀ (by positivity)]
      linarith
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt hbound hk_inv
  · -- rightCont
    intro t
    let N : ℕ := Nat.floor (t : ℝ) + 1
    have htN : (t : ℝ) < ((N + 1 : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (t : ℝ)
      push_cast [N]
      linarith
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    rcases hright t N htN (ε / 2) (half_pos hε) with ⟨δ, hδ_pos, hδ⟩
    let δ' : ℝ := min δ (((N + 1 : ℕ) : ℝ) - (t : ℝ))
    have hδ'_pos : 0 < δ' := lt_min hδ_pos (sub_pos.mpr htN)
    refine ⟨δ', hδ'_pos, fun s hs hds => ?_⟩
    have hs_ge : t ≤ s := hs
    have hs_lt : (s : ℝ) < (t : ℝ) + δ' := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hs_ge))] at hds
      linarith
    have hsN : (s : ℝ) < ((N + 1 : ℕ) : ℝ) := by
      have : δ' ≤ ((N + 1 : ℕ) : ℝ) - (t : ℝ) := min_le_right _ _
      linarith
    have hs_tδ : (s : ℝ) < (t : ℝ) + δ := by
      have : δ' ≤ δ := min_le_left _ _
      linarith
    rcases hright s N hsN (ε / 2) (half_pos hε) with ⟨δs, hδs_pos, hδs⟩
    let hi : ℝ := min ((s : ℝ) + δs) (min ((t : ℝ) + δ) ((N + 1 : ℕ) : ℝ))
    have hshi : (s : ℝ) < hi := lt_min (by linarith) (lt_min hs_tδ hsN)
    rcases exists_rat_btwn hshi with ⟨q, hsq, hqhi⟩
    have hq_nn : 0 ≤ q := Rat.cast_nonneg.mp ((NNReal.coe_nonneg s).trans hsq.le)
    have hq_le : q ≤ ((N + 1 : ℕ) : ℚ) := by
      have : (q : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := hqhi.le.trans ((min_le_right _ _).trans (min_le_right _ _))
      exact_mod_cast this
    let qd : RatDom (N + 1) := ⟨q, hq_nn, hq_le⟩
    have hs_lt_q : s < ratToNN qd := by
      rw [← NNReal.coe_lt_coe, ratToNN_coe]; exact hsq
    have ht_lt_q : t < ratToNN qd := lt_of_le_of_lt hs_ge hs_lt_q
    have h1 := hδs qd hs_lt_q (by rw [ratToNN_coe]; exact lt_of_lt_of_le hqhi (min_le_left _ _))
    have h2 := hδ qd ht_lt_q (by rw [ratToNN_coe]; exact lt_of_lt_of_le hqhi ((min_le_right _ _).trans (min_le_left _ _)))
    rw [Real.dist_eq]
    calc |rightLimVal f s - rightLimVal f t|
        = |(f (ratToNN qd) - rightLimVal f t) - (f (ratToNN qd) - rightLimVal f s)| := by ring_nf
      _ ≤ |f (ratToNN qd) - rightLimVal f t| + |f (ratToNN qd) - rightLimVal f s| := abs_sub _ _
      _ < ε / 2 + ε / 2 := add_lt_add h2 h1
      _ = ε := add_halves ε
  · -- leftLim
    intro t ht_pos
    let N : ℕ := Nat.floor (t : ℝ) + 1
    have htN : (t : ℝ) < ((N + 1 : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (t : ℝ)
      push_cast [N]
      linarith
    rcases hleft t ht_pos N htN.le with ⟨l, hl⟩
    refine ⟨l, ?_⟩
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    rcases hl (ε / 2) (half_pos hε) with ⟨δ, hδ_pos, hδ⟩
    refine ⟨δ, hδ_pos, fun s hs hds => ?_⟩
    have hs_lt : s < t := hs
    have hs_gt : (t : ℝ) - δ < (s : ℝ) := by
      rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hs_lt.le))] at hds
      linarith
    have hsN : (s : ℝ) < ((N + 1 : ℕ) : ℝ) := (NNReal.coe_lt_coe.mpr hs_lt).trans htN
    rcases hright s N hsN (ε / 2) (half_pos hε) with ⟨δs, hδs_pos, hδs⟩
    let hi : ℝ := min ((s : ℝ) + δs) (t : ℝ)
    have hshi : (s : ℝ) < hi := lt_min (by linarith) (NNReal.coe_lt_coe.mpr hs_lt)
    rcases exists_rat_btwn hshi with ⟨q, hsq, hqhi⟩
    have hq_nn : 0 ≤ q := Rat.cast_nonneg.mp ((NNReal.coe_nonneg s).trans hsq.le)
    have hq_le : q ≤ ((N + 1 : ℕ) : ℚ) := by
      have : (q : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := (hqhi.le.trans (min_le_right _ _)).trans htN.le
      exact_mod_cast this
    let qd : RatDom (N + 1) := ⟨q, hq_nn, hq_le⟩
    have hs_lt_q : s < ratToNN qd := by
      rw [← NNReal.coe_lt_coe, ratToNN_coe]; exact hsq
    have hq_lt_t : ratToNN qd < t := by
      rw [← NNReal.coe_lt_coe, ratToNN_coe]
      exact lt_of_lt_of_le hqhi (min_le_right _ _)
    have hq_gt : (t : ℝ) - δ < (ratToNN qd : ℝ) := by
      rw [ratToNN_coe]; linarith
    have h1 := hδs qd hs_lt_q (by rw [ratToNN_coe]; exact lt_of_lt_of_le hqhi (min_le_left _ _))
    have h2 := hδ qd hq_lt_t hq_gt
    rw [Real.dist_eq]
    calc |rightLimVal f s - l|
        = |(f (ratToNN qd) - l) - (f (ratToNN qd) - rightLimVal f s)| := by ring_nf
      _ ≤ |f (ratToNN qd) - l| + |f (ratToNN qd) - rightLimVal f s| := abs_sub _ _
      _ < ε / 2 + ε / 2 := add_lt_add h2 h1
      _ = ε := add_halves ε
  · -- noPosJumps
    intro t l ht_pos hl
    let N : ℕ := Nat.floor (t : ℝ) + 1
    have htN : (t : ℝ) < ((N + 1 : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (t : ℝ)
      push_cast [N]
      linarith
    rcases hleft t ht_pos N htN.le with ⟨l', hl'⟩
    -- First show l = l' via an explicit sequence s_k ↑ t
    have hll' : l = l' := by
      let seq : ℕ → NNReal := fun k => t * ((k + 1 : NNReal) / (k + 2 : NNReal))
      have hseq_lt : ∀ k : ℕ, seq k < t := fun k => by
        dsimp only [seq]
        have hlt1 : ((k + 1 : NNReal) / (k + 2 : NNReal)) < 1 := by
          rw [div_lt_one (by positivity)]
          exact_mod_cast Nat.lt_succ_self (k + 1)
        simpa using mul_lt_mul_of_pos_left hlt1 ht_pos
      have hseq_tend : Tendsto seq atTop (𝓝[<] t) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, Eventually.of_forall hseq_lt⟩
        have hdiv : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / ((k : ℝ) + 2)) atTop (𝓝 1) := by
          have hrew : (fun k : ℕ => ((k : ℝ) + 1) / ((k : ℝ) + 2)) =
              fun k : ℕ => 1 - 1 / ((k : ℝ) + 2) := by
            ext k
            have hne : (k : ℝ) + 2 ≠ 0 := by positivity
            field_simp [hne]; ring
          rw [hrew]
          have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) atTop (𝓝 0) := by
            have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
            refine h1.congr fun k => ?_
            change (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) = (1 : ℝ) / ((k : ℝ) + 2)
            push_cast; ring
          simpa using tendsto_const_nhds.sub h0
        have hcoe : Tendsto (fun k => (seq k : ℝ)) atTop (𝓝 (t : ℝ)) := by
          simpa [seq, mul_one] using hdiv.const_mul (t : ℝ)
        exact NNReal.tendsto_coe.mp hcoe
      have ht1 : Tendsto (fun k => rightLimVal f (seq k)) atTop (𝓝 l) := hl.comp hseq_tend
      have ht2 : Tendsto (fun k => rightLimVal f (seq k)) atTop (𝓝 l') := by
        -- From the leftLim proof above, rightLimVal f → l' along 𝓝[<] t
        have hl'_tend : Tendsto (rightLimVal f) (𝓝[<] t) (𝓝 l') := by
          rw [Metric.tendsto_nhdsWithin_nhds]
          intro ε hε
          rcases hl' (ε / 2) (half_pos hε) with ⟨δ, hδ_pos, hδ⟩
          refine ⟨δ, hδ_pos, fun s hs hds => ?_⟩
          have hs_lt : s < t := hs
          have hs_gt : (t : ℝ) - δ < (s : ℝ) := by
            rw [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hs_lt.le))] at hds
            linarith
          have hsN : (s : ℝ) < ((N + 1 : ℕ) : ℝ) := (NNReal.coe_lt_coe.mpr hs_lt).trans htN
          rcases hright s N hsN (ε / 2) (half_pos hε) with ⟨δs, hδs_pos, hδs⟩
          let hi : ℝ := min ((s : ℝ) + δs) (t : ℝ)
          have hshi : (s : ℝ) < hi := lt_min (by linarith) (NNReal.coe_lt_coe.mpr hs_lt)
          rcases exists_rat_btwn hshi with ⟨q, hsq, hqhi⟩
          have hq_nn : 0 ≤ q := Rat.cast_nonneg.mp ((NNReal.coe_nonneg s).trans hsq.le)
          have hq_le : q ≤ ((N + 1 : ℕ) : ℚ) := by
            have : (q : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := (hqhi.le.trans (min_le_right _ _)).trans htN.le
            exact_mod_cast this
          let qd : RatDom (N + 1) := ⟨q, hq_nn, hq_le⟩
          have hs_lt_q : s < ratToNN qd := by rw [← NNReal.coe_lt_coe, ratToNN_coe]; exact hsq
          have hq_lt_t : ratToNN qd < t := by
            rw [← NNReal.coe_lt_coe, ratToNN_coe]; exact lt_of_lt_of_le hqhi (min_le_right _ _)
          have hq_gt : (t : ℝ) - δ < (ratToNN qd : ℝ) := by rw [ratToNN_coe]; linarith
          have h1 := hδs qd hs_lt_q (by rw [ratToNN_coe]; exact lt_of_lt_of_le hqhi (min_le_left _ _))
          have h2 := hδ qd hq_lt_t hq_gt
          rw [Real.dist_eq]
          calc |rightLimVal f s - l'|
              = |(f (ratToNN qd) - l') - (f (ratToNN qd) - rightLimVal f s)| := by ring_nf
            _ ≤ |f (ratToNN qd) - l'| + |f (ratToNN qd) - rightLimVal f s| := abs_sub _ _
            _ < ε / 2 + ε / 2 := add_lt_add h2 h1
            _ = ε := add_halves ε
        exact hl'_tend.comp hseq_tend
      exact tendsto_nhds_unique ht1 ht2
    rw [hll']
    -- Now prove rightLimVal f t ≤ l' using RatNoPosJumps (N + 1)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rcases exists_nat_gt (3 / ε) with ⟨k, hk⟩
    have hk_lt : 1 / ((k : ℝ) + 1) < ε / 3 := by
      have hk1 : 3 / ε < (k : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hε] at hk1
      rw [div_lt_iff₀ (by positivity)]
      linarith
    rcases (hgoodN N).2.2.1 k with ⟨m, hm⟩
    rcases hright t N htN (ε / 3) (by positivity) with ⟨δR, hδR_pos, hδR⟩
    rcases hl' (ε / 3) (by positivity) with ⟨δL, hδL_pos, hδL⟩
    let halfM : ℝ := 1 / (2 * ((m : ℝ) + 1))
    let lo : ℝ := max 0 ((t : ℝ) - min δL halfM)
    have hlot : lo < (t : ℝ) := max_lt (NNReal.coe_pos.mpr ht_pos) (by
      have : 0 < min δL halfM := lt_min hδL_pos (by positivity)
      linarith)
    rcases exists_rat_btwn hlot with ⟨q1, hlo1, hq1t⟩
    let hi : ℝ := min ((N + 1 : ℕ) : ℝ) ((t : ℝ) + min δR halfM)
    have hthi : (t : ℝ) < hi := lt_min htN (by
      have : 0 < min δR halfM := lt_min hδR_pos (by positivity)
      linarith)
    rcases exists_rat_btwn hthi with ⟨q2, htq2, hq2hi⟩
    have hq1_nn : 0 ≤ q1 := Rat.cast_nonneg.mp ((le_max_left _ _).trans hlo1.le)
    have hq1_le : q1 ≤ ((N + 1 : ℕ) : ℚ) := by
      have : (q1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := hq1t.le.trans htN.le
      exact_mod_cast this
    have hq2_nn : 0 ≤ q2 := Rat.cast_nonneg.mp ((NNReal.coe_nonneg t).trans htq2.le)
    have hq2_le : q2 ≤ ((N + 1 : ℕ) : ℚ) := by
      have : (q2 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := hq2hi.le.trans (min_le_left _ _)
      exact_mod_cast this
    let qd1 : RatDom (N + 1) := ⟨q1, hq1_nn, hq1_le⟩
    let qd2 : RatDom (N + 1) := ⟨q2, hq2_nn, hq2_le⟩
    have hq12 : qd1.1 < qd2.1 := Rat.cast_lt.mp (hq1t.trans htq2)
    have hdiff : (qd2.1 : ℝ) - (qd1.1 : ℝ) < 1 / ((m : ℝ) + 1) := by
      have h1 : (t : ℝ) - halfM < (q1 : ℝ) := by
        have := lt_of_le_of_lt (le_max_right 0 ((t : ℝ) - min δL halfM)) hlo1
        linarith [min_le_right δL halfM]
      have h2 : (q2 : ℝ) < (t : ℝ) + halfM := by
        have := lt_of_lt_of_le hq2hi (min_le_right _ _)
        linarith [min_le_right δR halfM]
      have hsum : halfM + halfM = 1 / ((m : ℝ) + 1) := by
        dsimp only [halfM]
        have hne : (m : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hne]
        ring
      change (q2 : ℝ) - (q1 : ℝ) < 1 / ((m : ℝ) + 1)
      linarith
    have hjump := hm qd1 qd2 hq12 hdiff
    have hL1 : |f (ratToNN qd1) - l'| < ε / 3 := by
      refine hδL qd1 (by rw [← NNReal.coe_lt_coe, ratToNN_coe]; exact hq1t) ?_
      rw [ratToNN_coe]
      have := lt_of_le_of_lt (le_max_right 0 ((t : ℝ) - min δL halfM)) hlo1
      linarith [min_le_left δL halfM]
    have hR2 : |f (ratToNN qd2) - rightLimVal f t| < ε / 3 := by
      refine hδR qd2 (by rw [← NNReal.coe_lt_coe, ratToNN_coe]; exact htq2) ?_
      rw [ratToNN_coe]
      have := lt_of_lt_of_le hq2hi (min_le_right _ _)
      linarith [min_le_left δR halfM]
    have := (abs_lt.mp hL1).2
    have := (abs_lt.mp hR2).1
    linarith

private noncomputable def cadlagModify (f : NNReal → ℝ) : CadlagSNL := by
  classical
  exact if h : f ∈ Good then cadlagOfGood f h else cadlagZero

private lemma cadlagModify_val_of_good {f : NNReal → ℝ} (hf : f ∈ Good) (t : NNReal) :
    (cadlagModify f).val t = rightLimVal f t := by
  classical
  change (if h : f ∈ Good then cadlagOfGood f h else cadlagZero).val t = rightLimVal f t
  rw [dif_pos hf]
  rfl

private lemma measurable_cadlagModify :
    @Measurable (NNReal → ℝ) CadlagSNL inferInstance cadlagMS cadlagModify := by
  classical
  refine measurable_toCadlagSNL fun t => ?_
  have heq : (fun f => (cadlagModify f).val t) =
      fun f => if f ∈ Good then rightLimVal f t else 0 := by
    ext f
    by_cases hf : f ∈ Good
    · rw [if_pos hf, cadlagModify_val_of_good hf t]
    · rw [if_neg hf]
      change (if h : f ∈ Good then cadlagOfGood f h else cadlagZero).val t = 0
      rw [dif_neg hf]
      rfl
  rw [heq]
  exact Measurable.ite measurableSet_Good (measurable_rightLimVal t) measurable_const

/-! ### 5. Exponential martingale & Kolmogorov projective extension for `Q` -/

private noncomputable def expMart
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) (beta : ℝ) (t : NNReal) (ω : Omega) : ℝ :=
  esscherDensity L.X beta (L.ψ beta) t ω

private lemma expMart_nonneg
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) (beta : ℝ) (t : NNReal) (ω : Omega) :
    0 ≤ expMart L beta t ω :=
  (Real.exp_pos _).le

private lemma expMart_integrable
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) {beta : ℝ} (hBeta : 0 ≤ beta) (t : NNReal) :
    Integrable (expMart L beta t) P := by
  have heq : expMart L beta t =
      fun ω => Real.exp (-(L.ψ beta * (t : ℝ))) * Real.exp (beta * L.X t ω) := by
    ext ω
    dsimp only [expMart, esscherDensity]
    rw [← Real.exp_add]
    congr 1; ring
  rw [heq]
  exact (L.laplace t beta hBeta).1.const_mul _

private lemma integral_expMart_eq_one
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) {beta : ℝ} (hBeta : 0 ≤ beta) (t : NNReal) :
    ∫ ω, expMart L beta t ω ∂P = 1 := by
  have heq : expMart L beta t =
      fun ω => Real.exp (-(L.ψ beta * (t : ℝ))) * Real.exp (beta * L.X t ω) := by
    ext ω
    dsimp only [expMart, esscherDensity]
    rw [← Real.exp_add]
    congr 1; ring
  rw [heq, integral_const_mul, (L.laplace t beta hBeta).2, ← Real.exp_add]
  change Real.exp (-(L.ψ beta * (t : ℝ)) + (t : ℝ) * L.ψ beta) = 1
  have : -(L.ψ beta * (t : ℝ)) + (t : ℝ) * L.ψ beta = 0 := by ring
  rw [this, Real.exp_zero]

private lemma lintegral_expMart_set_eq
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) {beta : ℝ} (hBeta : 0 ≤ beta)
    {s t : NNReal} (hst : s ≤ t) {B : Set Omega} (hB : MeasurableSet[F s] B) :
    ∫⁻ ω in B, ENNReal.ofReal (expMart L beta t ω) ∂P =
      ∫⁻ ω in B, ENNReal.ofReal (expMart L beta s ω) ∂P := by
  have hBm : MeasurableSet B := F.le s B hB
  have hX_meas : ∀ u : NNReal, Measurable (L.X u) :=
    fun u => (L.adapted u).mono (F.le u) le_rfl
  let Z : NNReal → Omega → ℝ≥0∞ := fun u ω => ENNReal.ofReal (expMart L beta u ω)
  let W : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (beta * y - L.ψ beta * ((t - s : NNReal) : ℝ)))
  have hZ_measF : Measurable[F s] (Z s) := by
    have hXs : Measurable[F s] (L.X s) := L.adapted s
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((hXs.const_mul beta).sub measurable_const))
  have hW_meas : Measurable W := by fun_prop
  have hfac : ∀ ω, B.indicator (Z t) ω = W (L.X t ω - L.X s ω) * B.indicator (Z s) ω := by
    intro ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      dsimp only [Z, W, expMart, esscherDensity]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      rw [NNReal.coe_sub hst]
      ring
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, mul_zero]
  have hinc_meas : Measurable (fun ω => L.X t ω - L.X s ω) := (hX_meas t).sub (hX_meas s)
  have hf_meas : Measurable[MeasurableSpace.comap (fun ω => L.X t ω - L.X s ω) inferInstance]
      (fun ω => W (L.X t ω - L.X s ω)) :=
    hW_meas.comp (Measurable.of_comap_le le_rfl)
  have hg_meas : Measurable[F s] (B.indicator (Z s)) := hZ_measF.indicator hB
  have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (measurable_iff_comap_le.mp hinc_meas) (F.le s) (L.indepIncrements s t hst) hf_meas hg_meas
  have hW_int : ∫⁻ ω, W (L.X t ω - L.X s ω) ∂P = 1 := by
    have hident := (L.stationaryIncrements s t hst).comp hW_meas
    change ∫⁻ ω, (W ∘ fun ω => L.X t ω - L.X s ω) ω ∂P = 1
    rw [hident.lintegral_eq]
    have h1 := integral_expMart_eq_one L hBeta (t - s)
    change ∫⁻ ω, ENNReal.ofReal (expMart L beta (t - s) ω) ∂P = 1
    rw [← ofReal_integral_eq_lintegral_ofReal (expMart_integrable L hBeta (t - s))
      (ae_of_all _ (expMart_nonneg L beta (t - s))), h1, ENNReal.ofReal_one]
  rw [← lintegral_indicator hBm, ← lintegral_indicator hBm]
  have hfun : B.indicator (fun ω => ENNReal.ofReal (expMart L beta t ω)) =
      fun ω => W (L.X t ω - L.X s ω) * B.indicator (fun ω => ENNReal.ofReal (expMart L beta s ω)) ω := by
    ext ω
    by_cases hω : ω ∈ B
    · simpa [Z, hω] using hfac ω
    · simp [hω]
  rw [hfun, hmul, hW_int, one_mul]

/-! ### 6. Measurability of `firstHittingTime` and `Antitone` on `CadlagSNL` -/

private lemma antitone_iff_rat (p : CadlagSNL) :
    Antitone p.val ↔
      ∀ (q1 q2 : ℚ), 0 ≤ q1 → q1 ≤ q2 →
        p.val (Real.toNNReal (q2 : ℝ)) ≤ p.val (Real.toNNReal (q1 : ℝ)) := by
  constructor
  · intro h q1 q2 hq1 h12
    refine h ?_
    rw [← NNReal.coe_le_coe,
      Real.coe_toNNReal (q1 : ℝ) (Rat.cast_nonneg.mpr hq1),
      Real.coe_toNNReal (q2 : ℝ) (Rat.cast_nonneg.mpr (hq1.trans h12))]
    exact Rat.cast_le.mpr h12
  · intro h s t hst
    -- Take ratAbove s k and ratAbove t k; for large k, ratAbove s k ≤ ratAbove t k or compare directly
    have hs_tend : Tendsto (fun k => p.val (ratAbove s k)) atTop (𝓝 (p.val s)) :=
      (p.rightCont s).tendsto.comp (ratAbove_tendsto s)
    have ht_tend : Tendsto (fun k => p.val (ratAbove t k)) atTop (𝓝 (p.val t)) :=
      (p.rightCont t).tendsto.comp (ratAbove_tendsto t)
    refine le_of_tendsto_of_tendsto' ht_tend hs_tend fun k => ?_
    rcases ratAbove_isRat s k with ⟨q1, hq1, h1eq⟩
    rcases ratAbove_isRat t k with ⟨q2, hq2, h2eq⟩
    rw [← h1eq, ← h2eq]
    refine h q1 q2 hq1 ?_
    have h12 : ratAbove s k ≤ ratAbove t k := by
      dsimp only [ratAbove]
      refine div_le_div_of_nonneg_right ?_ bot_le
      have hfl : Nat.floor ((s : ℝ) * ((k : ℝ) + 1)) ≤ Nat.floor ((t : ℝ) * ((k : ℝ) + 1)) :=
        Nat.floor_mono (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hst) (by positivity))
      exact_mod_cast Nat.add_le_add_right hfl 1
    have hcoe : (q1 : ℝ) ≤ (q2 : ℝ) := by
      rw [← Real.coe_toNNReal (q1 : ℝ) (Rat.cast_nonneg.mpr hq1),
        ← Real.coe_toNNReal (q2 : ℝ) (Rat.cast_nonneg.mpr hq2), h1eq, h2eq]
      exact NNReal.coe_le_coe.mpr h12
    exact Rat.cast_le.mp hcoe

private lemma measurableSet_antitone_cadlag :
    @MeasurableSet CadlagSNL cadlagMS {p : CadlagSNL | Antitone p.val} := by
  let _ : MeasurableSpace CadlagSNL := cadlagMS
  have heq : {p : CadlagSNL | Antitone p.val} =
      ⋂ q1 : ℚ, ⋂ q2 : ℚ, ⋂ (_ : 0 ≤ q1), ⋂ (_ : q1 ≤ q2),
        {p : CadlagSNL | p.val (Real.toNNReal (q2 : ℝ)) ≤ p.val (Real.toNNReal (q1 : ℝ))} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
    exact antitone_iff_rat p
  rw [heq]
  refine MeasurableSet.iInter fun q1 => MeasurableSet.iInter fun q2 =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
  have hm1 : Measurable (fun p : CadlagSNL => p.val (Real.toNNReal (q1 : ℝ))) :=
    (measurable_pi_apply _).comp measurable_cadlagVal
  have hm2 : Measurable (fun p : CadlagSNL => p.val (Real.toNNReal (q2 : ℝ))) :=
    (measurable_pi_apply _).comp measurable_cadlagVal
  exact measurableSet_le hm2 hm1

private lemma measurable_cadlag_firstHittingTime (x : ℝ) :
    @Measurable CadlagSNL (WithTop NNReal) cadlagMS inferInstance
      (fun p : CadlagSNL => firstHittingTime (fun t (p : CadlagSNL) => p.val t) (Set.Ioi x) p) := by
  let _ : MeasurableSpace CadlagSNL := cadlagMS
  refine measurable_of_Iio fun a => ?_
  have hlt_meas : ∀ t : NNReal,
      MeasurableSet {p : CadlagSNL | firstHittingTime (fun s (p : CadlagSNL) => p.val s) (Set.Ioi x) p < (t : WithTop NNReal)} := by
    intro t
    have heq : {p : CadlagSNL | firstHittingTime (fun s (p : CadlagSNL) => p.val s) (Set.Ioi x) p < (t : WithTop NNReal)} =
        ⋃ q : {q : ℚ // 0 < q ∧ Real.toNNReal (q : ℝ) < t},
          {p : CadlagSNL | x < p.val (Real.toNNReal (q.1 : ℝ))} := by
      ext p
      simp only [mem_ofPred_eq, firstHittingTime, sInf_lt_iff, mem_image,
        exists_exists_and_eq_and, mem_iUnion]
      constructor
      · rintro ⟨s, ⟨hs_pos, hps⟩, hs_lt⟩
        have hs_lt' : s < t := WithTop.coe_lt_coe.mp hs_lt
        have hps' : x < p.val s := hps
        rcases Metric.continuousWithinAt_iff.mp (p.rightCont s) (p.val s - x) (sub_pos.mpr hps') with
          ⟨δ, hδ_pos, hδ⟩
        let hi : ℝ := min (t : ℝ) ((s : ℝ) + δ)
        have hs_hi : (s : ℝ) < hi := lt_min (NNReal.coe_lt_coe.mpr hs_lt') (by linarith)
        rcases exists_rat_btwn hs_hi with ⟨q, hsq, hqhi⟩
        have hq_pos : (0 : ℚ) < q := Rat.cast_pos.mp ((NNReal.coe_pos.mpr hs_pos).trans hsq)
        have hq_nn : ((Real.toNNReal (q : ℝ)) : ℝ) = (q : ℝ) :=
          Real.coe_toNNReal (q : ℝ) (Rat.cast_nonneg.mpr hq_pos.le)
        have hq_lt_t : Real.toNNReal (q : ℝ) < t := by
          rw [← NNReal.coe_lt_coe, hq_nn]; exact lt_of_lt_of_le hqhi (min_le_left _ _)
        have hs_le_q : s ≤ Real.toNNReal (q : ℝ) := by
          rw [← NNReal.coe_le_coe, hq_nn]; exact hsq.le
        have hdist : dist (Real.toNNReal (q : ℝ)) s < δ := by
          rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (by rw [hq_nn]; exact hsq.le)), hq_nn]
          linarith [lt_of_lt_of_le hqhi (min_le_right _ _)]
        have hXdist := hδ hs_le_q hdist
        rw [Real.dist_eq] at hXdist
        exact ⟨⟨q, hq_pos, hq_lt_t⟩, by linarith [(abs_lt.mp hXdist).1]⟩
      · rintro ⟨⟨q, hq_pos, hq_lt⟩, hXq⟩
        have hq_nn : ((Real.toNNReal (q : ℝ)) : ℝ) = (q : ℝ) :=
          Real.coe_toNNReal (q : ℝ) (Rat.cast_nonneg.mpr hq_pos.le)
        have hq_pos' : (0 : NNReal) < Real.toNNReal (q : ℝ) := by
          rw [← NNReal.coe_lt_coe, NNReal.coe_zero, hq_nn]; exact Rat.cast_pos.mpr hq_pos
        exact ⟨Real.toNNReal (q : ℝ), ⟨hq_pos', hXq⟩, WithTop.coe_lt_coe.mpr hq_lt⟩
    rw [heq]
    exact MeasurableSet.iUnion fun q =>
      ((measurable_pi_apply _).comp measurable_cadlagVal) measurableSet_Ioi
  cases a with
  | top =>
    have heq : (fun p : CadlagSNL => firstHittingTime (fun s (p : CadlagSNL) => p.val s) (Set.Ioi x) p) ⁻¹' Iio (⊤ : WithTop NNReal) =
        ⋃ n : ℕ, {p : CadlagSNL | firstHittingTime (fun s (p : CadlagSNL) => p.val s) (Set.Ioi x) p < ((n : NNReal) : WithTop NNReal)} := by
      ext p
      simp only [mem_preimage, mem_Iio, mem_iUnion, mem_ofPred_eq]
      constructor
      · intro h
        cases hτ : firstHittingTime (fun s (p : CadlagSNL) => p.val s) (Set.Ioi x) p with
        | top => simp [hτ] at h
        | coe t =>
          rcases exists_nat_gt (t : ℝ) with ⟨n, hn⟩
          exact ⟨n, WithTop.coe_lt_coe.mpr (by exact_mod_cast hn)⟩
      · rintro ⟨n, hn⟩
        exact lt_trans hn (WithTop.coe_lt_top _)
    rw [heq]
    exact MeasurableSet.iUnion fun n => hlt_meas n
  | coe t =>
    exact hlt_meas t

end Kyprianou.Ch03.CanonicalEsscherUncompletedProof

open Kyprianou.Ch03 Kyprianou.Ch03.CanonicalEsscherUncompletedProof

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (beta : Real) (hBeta : 0 <= beta) :
    exists (Omega1 : Type) (m1 : MeasurableSpace Omega1),
      letI : MeasurableSpace Omega1 := m1
      exists (P1 Q1 : Measure Omega1)
             (hP1 : IsProbabilityMeasure P1)
             (hQ1 : IsProbabilityMeasure Q1)
             (F1 : Filtration NNReal m1)
             (L0 : AvramDividend.Classical.SpectrallyNegativeLevy P1 F1),
        (forall theta : Real, L0.ψ theta = L.ψ theta) ∧
        ((¬ (∀ᵐ omega : Omega ∂ P, Antitone (fun t : NNReal => L.X t omega))) ->
          ¬ (∀ᵐ omega : Omega1 ∂ P1, Antitone (fun t : NNReal => L0.X t omega))) ∧
        Measure.map
          (fun omega : Omega1 =>
            fun x : NNReal =>
              firstHittingTime L0.X (Set.Ioi (x : Real)) omega) P1 =
        Measure.map
          (fun omega : Omega =>
            fun x : NNReal =>
              firstHittingTime L.X (Set.Ioi (x : Real)) omega) P ∧
        (forall (t : NNReal) (A : Set Omega1),
          MeasurableSet[F1 t] A ->
          Q1 A =
            ENNReal.ofReal
              (∫ omega, Set.indicator A
                (fun omega : Omega1 =>
                  esscherDensity L0.X beta (L0.ψ beta) t omega)
                omega ∂P1)) := by
  let _ : MeasurableSpace CadlagSNL := cadlagMS
  have hX_meas : ∀ t : NNReal, Measurable (L.X t) :=
    fun t => (L.adapted t).mono (F.le t) le_rfl
  let pathOf : Omega → CadlagSNL := fun ω =>
    ⟨fun t => L.X t ω, L.X_zero ω, L.rightCont ω, L.leftLim ω, L.noPosJumps ω⟩
  have hpath_meas : Measurable pathOf := measurable_toCadlagSNL hX_meas
  let P1 : Measure CadlagSNL := P.map pathOf
  have hP1 : IsProbabilityMeasure P1 := Measure.isProbabilityMeasure_map hpath_meas.aemeasurable
  let evalPath : Omega → NNReal → ℝ := fun ω t => L.X t ω
  have hevalPath_meas : Measurable evalPath := measurable_pi_lambda _ hX_meas
  let μP : Measure (NNReal → ℝ) := P.map evalPath
  have hμP : IsProbabilityMeasure μP := Measure.isProbabilityMeasure_map hevalPath_meas.aemeasurable
  have hμP_eq : μP = P1.map CadlagSNL.val := by
    dsimp only [μP, P1]
    rw [Measure.map_map measurable_cadlagVal hpath_meas]
    rfl
  -- Step A: Build L0 : SpectrallyNegativeLevy P1 cadlagFiltr
  have hcomap_F1 : ∀ s : NNReal,
      MeasurableSpace.comap pathOf (cadlagFiltr s) ≤ F s := by
    intro s
    dsimp only [cadlagFiltr, PerfCorrMSQ.natFiltr]
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun u => ?_
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun hu => ?_
    rw [MeasurableSpace.comap_comp]
    exact (measurable_iff_comap_le.mp (L.adapted u)).trans (F.mono hu)
  let L0 : AvramDividend.Classical.SpectrallyNegativeLevy P1 cadlagFiltr := {
    X := fun t p => p.val t
    c := L.c
    σ := L.σ
    ν := L.ν
    isProbability := hP1
    σ_nonneg := L.σ_nonneg
    ν_Ici := L.ν_Ici
    ν_integrable := L.ν_integrable
    X_zero := fun p => p.val_zero
    rightCont := fun p => p.rightCont
    leftLim := fun p => p.leftLim
    noPosJumps := fun p => p.noPosJumps
    adapted := fun t =>
      measurable_iff_comap_le.mpr (le_iSup₂_of_le t le_rfl le_rfl)
    indepIncrements := fun s t hst => by
      rw [ProbabilityTheory.Indep_iff]
      rintro A B ⟨U, hU, rfl⟩ hB
      have hA_m : MeasurableSet ((fun p : CadlagSNL => p.val t - p.val s) ⁻¹' U) :=
        (((measurable_pi_apply t).comp measurable_cadlagVal).sub
          ((measurable_pi_apply s).comp measurable_cadlagVal)) hU
      have hB_m : MeasurableSet B := cadlagFiltr.le s B hB
      rw [Measure.map_apply hpath_meas (hA_m.inter hB_m),
        Measure.map_apply hpath_meas hA_m,
        Measure.map_apply hpath_meas hB_m,
        Set.preimage_inter]
      have hA_pre : MeasurableSet[MeasurableSpace.comap (fun ω => L.X t ω - L.X s ω) inferInstance]
          (pathOf ⁻¹' ((fun p : CadlagSNL => p.val t - p.val s) ⁻¹' U)) :=
        ⟨U, hU, rfl⟩
      have hB_pre : MeasurableSet[F s] (pathOf ⁻¹' B) :=
        hcomap_F1 s _ ⟨B, hB, rfl⟩
      exact (ProbabilityTheory.Indep_iff _ _ _).mp (L.indepIncrements s t hst) _ _ hA_pre hB_pre
    stationaryIncrements := fun s t hst => by
      have hsub_m : Measurable (fun p : CadlagSNL => p.val t - p.val s) :=
        ((measurable_pi_apply t).comp measurable_cadlagVal).sub
          ((measurable_pi_apply s).comp measurable_cadlagVal)
      have hts_m : Measurable (fun p : CadlagSNL => p.val (t - s)) :=
        (measurable_pi_apply (t - s)).comp measurable_cadlagVal
      have h1 : IdentDistrib (fun p : CadlagSNL => p.val t - p.val s) (fun ω => L.X t ω - L.X s ω) P1 P := by
        refine ⟨hsub_m.aemeasurable, ((hX_meas t).sub (hX_meas s)).aemeasurable, ?_⟩
        dsimp only [P1]
        rw [Measure.map_map hsub_m hpath_meas]
        rfl
      have h2 : IdentDistrib (fun ω => L.X (t - s) ω) (fun p : CadlagSNL => p.val (t - s)) P P1 := by
        refine ⟨(hX_meas (t - s)).aemeasurable, hts_m.aemeasurable, ?_⟩
        dsimp only [P1]
        rw [Measure.map_map hts_m hpath_meas]
        rfl
      exact (h1.trans (L.stationaryIncrements s t hst)).trans h2
    laplace := fun t θ hθ => by
      have hmeas_exp : Measurable (fun p : CadlagSNL => Real.exp (θ * p.val t)) :=
        Real.measurable_exp.comp (((measurable_pi_apply t).comp measurable_cadlagVal).const_mul θ)
      refine ⟨?_, ?_⟩
      · exact (integrable_map_measure hmeas_exp.aestronglyMeasurable hpath_meas.aemeasurable).mpr
          (L.laplace t θ hθ).1
      · rw [integral_map hpath_meas.aemeasurable hmeas_exp.aestronglyMeasurable]
        exact (L.laplace t θ hθ).2
  }
  -- Step B: Build projective family of Esscher-tilted finite-dimensional laws and apply Kolmogorov extension
  let Ptilt : NNReal → Measure Omega := fun T =>
    P.withDensity (fun ω => ENNReal.ofReal (expMart L beta T ω))
  have hPtilt_prob : ∀ T : NNReal, IsProbabilityMeasure (Ptilt T) := by
    intro T
    refine ⟨?_⟩
    dsimp only [Ptilt]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal (expMart_integrable L hBeta T)
      (ae_of_all _ (expMart_nonneg L beta T)), integral_expMart_eq_one L hBeta T, ENNReal.ofReal_one]
  have hPtilt_eq : ∀ {s t : NNReal}, s ≤ t → ∀ {B : Set Omega}, MeasurableSet[F s] B →
      Ptilt t B = Ptilt s B := by
    intro s t hst B hB
    have hBm : MeasurableSet B := F.le s B hB
    dsimp only [Ptilt]
    rw [withDensity_apply _ hBm, withDensity_apply _ hBm]
    exact lintegral_expMart_set_eq L hBeta hst hB
  let Q_fam : ∀ I : Finset NNReal, Measure (∀ t : I, ℝ) := fun I =>
    (Ptilt (I.sup id)).map (fun ω (t : I) => L.X t.1 ω)
  have hmap_meas : ∀ I : Finset NNReal, Measurable (fun ω (t : I) => L.X t.1 ω) :=
    fun I => measurable_pi_lambda _ fun t => hX_meas t.1
  have hmap_measF : ∀ I : Finset NNReal,
      Measurable[F (I.sup id)] (fun ω (t : I) => L.X t.1 ω) := fun I =>
    @measurable_pi_lambda Omega I (fun _ => ℝ) (F (I.sup id)) _ _ fun t =>
      (L.adapted t.1).mono (F.mono (Finset.le_sup (f := id) t.2)) le_rfl
  let pf : LevyFoundations.ProjectiveFamily NNReal (fun _ : NNReal => ℝ) := {
    measure := Q_fam
    prob := fun I =>
      letI := hPtilt_prob (I.sup id)
      Measure.isProbabilityMeasure_map (hmap_meas I).aemeasurable
    consistent := by
      intro I J hJI
      ext E hE
      have hsup : J.sup id ≤ I.sup id := Finset.sup_mono hJI
      have hrm : Measurable (Finset.restrict₂ (π := fun _ : NNReal => ℝ) hJI) :=
        Finset.measurable_restrict₂ (X := fun _ : NNReal => ℝ) hJI
      rw [Measure.map_apply hrm hE,
        Measure.map_apply (hmap_meas I) (hrm hE),
        Measure.map_apply (hmap_meas J) hE]
      have hpre_eq : (fun ω (t : I) => L.X t.1 ω) ⁻¹'
          (Finset.restrict₂ (π := fun _ : NNReal => ℝ) hJI ⁻¹' E) =
          (fun ω (t : J) => L.X t.1 ω) ⁻¹' E := rfl
      rw [hpre_eq]
      exact (hPtilt_eq hsup ((hmap_measF J) hE)).symm
  }
  rcases levy_foundations_kolmogorovExtension_exists pf with ⟨μQ, hProj⟩
  have hμQ_prob : IsProbabilityMeasure μQ := by
    refine ⟨?_⟩
    have h0 := hProj ∅
    have huniv : μQ Set.univ = Q_fam ∅ Set.univ := by
      have := congrArg (fun ν : Measure (∀ _ : (∅ : Finset NNReal), ℝ) => ν Set.univ) h0
      simpa [Measure.map_apply (Finset.measurable_restrict (X := fun _ : NNReal => ℝ) ∅) MeasurableSet.univ] using this
    rw [huniv]
    have _ := pf.prob ∅
    exact measure_univ
  -- Step C: μQ agrees with Esscher-tilted μP on natFiltr eval t for every t
  let evalF : NNReal → (NNReal → ℝ) → ℝ := fun s f => f s
  have hEssF_meas : ∀ t : NNReal,
      Measurable (fun f : NNReal → ℝ => ENNReal.ofReal (esscherDensity evalF beta (L.ψ beta) t f)) := fun t => by
    change Measurable (fun f : NNReal → ℝ => ENNReal.ofReal (Real.exp (beta * f t - L.ψ beta * (t : ℝ))))
    have h1 : Measurable (fun f : NNReal → ℝ => f t) := measurable_pi_apply t
    exact (Real.measurable_exp.comp ((h1.const_mul beta).sub_const (L.ψ beta * (t : ℝ)))).ennreal_ofReal
  have hμQ_natFiltr : ∀ (t : NNReal) (A : Set (NNReal → ℝ)),
      MeasurableSet[PerfCorrMSQ.natFiltr evalF t] A →
      μQ A = ∫⁻ f in A, ENNReal.ofReal (esscherDensity evalF beta (L.ψ beta) t f) ∂μP := by
    intro t
    let νt : Measure (NNReal → ℝ) :=
      μP.withDensity (fun f => ENNReal.ofReal (esscherDensity evalF beta (L.ψ beta) t f))
    have hνt_prob : IsProbabilityMeasure νt := by
      refine ⟨?_⟩
      dsimp only [νt, μP]
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        lintegral_map (hEssF_meas t) hevalPath_meas]
      have h1 := integral_expMart_eq_one L hBeta t
      change ∫⁻ ω, ENNReal.ofReal (expMart L beta t ω) ∂P = 1
      rw [← ofReal_integral_eq_lintegral_ofReal (expMart_integrable L hBeta t)
        (ae_of_all _ (expMart_nonneg L beta t)), h1, ENNReal.ofReal_one]
    have hνt_eq : ∀ A : Set (NNReal → ℝ), MeasurableSet A →
        νt A = ∫⁻ f in A, ENNReal.ofReal (esscherDensity evalF beta (L.ψ beta) t f) ∂μP :=
      fun A hA => withDensity_apply _ hA
    intro A hA
    rw [← hνt_eq A (natFiltr_le_pi t A hA)]
    refine MeasurableSpace.induction_on_inter
      (m := PerfCorrMSQ.natFiltr evalF t)
      (C := fun B _ => μQ B = νt B)
      (natFiltr_eval_eq_generateFrom_cylinders t)
      (isPiSystem_cylinders t)
      ?_ ?_ ?_ ?_ A hA
    · simp
    · rintro B ⟨I, hI, E, hE, rfl⟩
      have hsup : I.sup id ≤ t := Finset.sup_le fun s hs => hI s hs
      have hrm : Measurable (I.restrict (π := fun _ : NNReal => ℝ)) :=
        Finset.measurable_restrict (X := fun _ : NNReal => ℝ) I
      have hL : μQ (I.restrict ⁻¹' E) = Q_fam I E := by
        have h := congrArg (fun ν : Measure (∀ s : I, ℝ) => ν E) (hProj I)
        rw [Measure.map_apply hrm hE] at h
        exact h
      have hR : νt (I.restrict ⁻¹' E) = Ptilt t ((fun ω (s : I) => L.X s.1 ω) ⁻¹' E) := by
        have hBm : MeasurableSet (I.restrict ⁻¹' E) := hrm hE
        rw [hνt_eq _ hBm]
        dsimp only [μP, Ptilt]
        rw [withDensity_apply _ ((hmap_meas I) hE),
          setLIntegral_map hBm (hEssF_meas t) hevalPath_meas]
        rfl
      rw [hL, hR]
      dsimp only [Q_fam]
      rw [Measure.map_apply (hmap_meas I) hE]
      exact (hPtilt_eq hsup ((hmap_measF I) hE)).symm
    · intro B hBm hEq
      have hBpi : MeasurableSet B := natFiltr_le_pi t B hBm
      rw [measure_compl hBpi (measure_ne_top μQ B),
        measure_compl hBpi (measure_ne_top νt B),
        measure_univ, measure_univ, hEq]
    · intro g hdisj hgm hEq
      have hgpi : ∀ i, MeasurableSet (g i) := fun i => natFiltr_le_pi t _ (hgm i)
      rw [measure_iUnion hdisj hgpi, measure_iUnion hdisj hgpi]
      exact tsum_congr hEq
  -- Step D: μQ (Good) = 1 and ∀ t, (cadlagModify f).val t = f t μQ-a.e.
  have hμQ_Good : μQ Goodᶜ = 0 := by
    have hcomp : Goodᶜ = ⋃ N : ℕ, (GoodN (N + 1))ᶜ := by
      dsimp only [Good]; rw [Set.compl_iInter]
    rw [hcomp]
    refine measure_iUnion_null fun N => ?_
    have hGm : MeasurableSet[PerfCorrMSQ.natFiltr evalF ((N + 1 : ℕ) : NNReal)] (GoodN (N + 1))ᶜ :=
      (measurableSet_GoodN (N + 1)).compl
    rw [hμQ_natFiltr ((N + 1 : ℕ) : NNReal) _ hGm]
    have hμP_zero : μP (GoodN (N + 1))ᶜ = 0 := by
      dsimp only [μP]
      rw [Measure.map_apply hevalPath_meas (natFiltr_le_pi _ _ hGm)]
      have hemp : evalPath ⁻¹' (GoodN (N + 1))ᶜ = ∅ := by
        ext ω
        simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
        exact cadlagSNL_mem_GoodN (pathOf ω) (N + 1)
      rw [hemp, measure_empty]
    exact setLIntegral_measure_zero _ _ hμP_zero
  have hμQ_ae_eq : ∀ t : NNReal, ∀ᵐ f ∂μQ, (cadlagModify f).val t = f t := by
    intro t
    let N : ℕ := Nat.floor (t : ℝ) + 2
    have ht_le : t ≤ (N : NNReal) := by
      rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
      have := (Nat.lt_floor_add_one (t : ℝ)).le
      push_cast [N]
      linarith
    have hrab_le : ∀ k : ℕ, ratAbove t k ≤ (N : NNReal) := fun k => by
      rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
      have h1 := ratAbove_le t k
      have h2 : 1 / ((k : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
      have h3 := (Nat.lt_floor_add_one (t : ℝ)).le
      push_cast [N]
      linarith
    let Eqt : Set (NNReal → ℝ) := {f | Tendsto (fun k : ℕ => f (ratAbove t k)) atTop (𝓝 (f t))}
    have hEqt_measF : MeasurableSet[PerfCorrMSQ.natFiltr evalF (N : NNReal)] Eqt := by
      have heq : Eqt = ⋂ j : ℕ, ⋃ K : ℕ, ⋂ k : ℕ, ⋂ (_ : K ≤ k),
          {f : NNReal → ℝ | |f (ratAbove t k) - f t| < 1 / ((j : ℝ) + 1)} := by
        ext f
        simp only [Eqt, Metric.tendsto_atTop, Real.dist_eq, mem_ofPred_eq, mem_iInter, mem_iUnion]
        constructor
        · intro h j
          rcases h (1 / ((j : ℝ) + 1)) (by positivity) with ⟨K, hK⟩
          exact ⟨K, fun k hk => hK k hk⟩
        · intro h ε hε
          rcases exists_nat_gt (1 / ε) with ⟨j, hj⟩
          have hj_lt : 1 / ((j : ℝ) + 1) < ε := by
            have hj1 : 1 / ε < (j : ℝ) + 1 := by linarith
            rw [div_lt_iff₀ hε] at hj1
            rw [div_lt_iff₀ (by positivity)]
            linarith
          rcases h j with ⟨K, hK⟩
          exact ⟨K, fun k hk => (hK k hk).trans hj_lt⟩
      rw [heq]
      have hmt : @Measurable (NNReal → ℝ) ℝ (PerfCorrMSQ.natFiltr evalF (N : NNReal)) inferInstance
          (fun f => f t) :=
        measurable_iff_comap_le.mpr (le_iSup₂_of_le t ht_le le_rfl)
      have hmk : ∀ k, @Measurable (NNReal → ℝ) ℝ (PerfCorrMSQ.natFiltr evalF (N : NNReal)) inferInstance
          (fun f => f (ratAbove t k)) := fun k =>
        measurable_iff_comap_le.mpr (le_iSup₂_of_le (ratAbove t k) (hrab_le k) le_rfl)
      exact MeasurableSet.iInter fun j => MeasurableSet.iUnion fun K =>
        MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
          (continuous_abs.measurable.comp ((hmk k).sub hmt)) measurableSet_Iio
    have hμQ_Eqt : μQ Eqtᶜ = 0 := by
      rw [hμQ_natFiltr (N : NNReal) Eqtᶜ hEqt_measF.compl]
      have hμP_zero : μP Eqtᶜ = 0 := by
        dsimp only [μP]
        rw [Measure.map_apply hevalPath_meas (natFiltr_le_pi _ _ hEqt_measF.compl)]
        have hemp : evalPath ⁻¹' Eqtᶜ = ∅ := by
          ext ω
          simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not, Eqt, evalPath]
          exact (L.rightCont ω t).tendsto.comp (ratAbove_tendsto t)
        rw [hemp, measure_empty]
      exact setLIntegral_measure_zero _ _ hμP_zero
    have hGood_ae : ∀ᵐ f ∂μQ, f ∈ Good := ae_iff.mpr hμQ_Good
    have hEqt_ae : ∀ᵐ f ∂μQ, f ∈ Eqt := ae_iff.mpr hμQ_Eqt
    filter_upwards [hGood_ae, hEqt_ae] with f hfG hfE
    rw [cadlagModify_val_of_good hfG t]
    exact rightLimVal_eq_of_tendsto hfE
  -- Step E: Define Q1 = μQ.map cadlagModify and verify Esscher density on cadlagFiltr t
  let Q1 : Measure CadlagSNL := μQ.map cadlagModify
  have hQ1 : IsProbabilityMeasure Q1 := Measure.isProbabilityMeasure_map measurable_cadlagModify.aemeasurable
  refine ⟨CadlagSNL, cadlagMS, P1, Q1, hP1, hQ1, cadlagFiltr, L0, ?_, ?_, ?_, ?_⟩
  · -- (1) L0.ψ = L.ψ
    intro _
    rfl
  · -- (2) non-antitone preserved
    intro hNotDec hAnti1
    apply hNotDec
    have hP1_zero : P1 {p : CadlagSNL | Antitone p.val}ᶜ = 0 := ae_iff.mp hAnti1
    rw [ae_iff]
    have hpre : pathOf ⁻¹' {p : CadlagSNL | Antitone p.val}ᶜ =
        {ω : Omega | ¬ Antitone (fun t : NNReal => L.X t ω)} := rfl
    rw [← hpre, ← Measure.map_apply hpath_meas measurableSet_antitone_cadlag.compl]
    exact hP1_zero
  · -- (3) first-hitting-time process law preserved
    have hhit_meas : Measurable (fun (p : CadlagSNL) (x : NNReal) =>
        firstHittingTime L0.X (Set.Ioi (x : ℝ)) p) :=
      measurable_pi_lambda _ fun x => measurable_cadlag_firstHittingTime (x : ℝ)
    dsimp only [P1]
    rw [Measure.map_map hhit_meas hpath_meas]
    rfl
  · -- (4) Esscher density on cadlagFiltr t
    intro t A hA
    have hAm : MeasurableSet A := cadlagFiltr.le t A hA
    have hEss_int : Integrable (esscherDensity L0.X beta (L0.ψ beta) t) P1 :=
      expMart_integrable L0 hBeta t
    have hEss_nn : ∀ p : CadlagSNL, 0 ≤ esscherDensity L0.X beta (L0.ψ beta) t p :=
      fun _ => (Real.exp_pos _).le
    have hrhs_eq : ENNReal.ofReal
        (∫ p, A.indicator (fun p : CadlagSNL => esscherDensity L0.X beta (L0.ψ beta) t p) p ∂P1) =
        ∫⁻ p in A, ENNReal.ofReal (esscherDensity L0.X beta (L0.ψ beta) t p) ∂P1 := by
      rw [integral_indicator hAm,
        ofReal_integral_eq_lintegral_ofReal hEss_int.integrableOn (ae_of_all _ hEss_nn)]
    rw [hrhs_eq]
    let ν1 : Measure CadlagSNL :=
      P1.withDensity (fun p => ENNReal.ofReal (esscherDensity L0.X beta (L0.ψ beta) t p))
    have hν1_prob : IsProbabilityMeasure ν1 := by
      refine ⟨?_⟩
      dsimp only [ν1]
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← ofReal_integral_eq_lintegral_ofReal hEss_int (ae_of_all _ hEss_nn)]
      change ENNReal.ofReal (∫ p, expMart L0 beta t p ∂P1) = 1
      rw [integral_expMart_eq_one L0 hBeta t, ENNReal.ofReal_one]
    have hν1_apply : ∀ B : Set CadlagSNL, MeasurableSet B →
        ν1 B = ∫⁻ p in B, ENNReal.ofReal (esscherDensity L0.X beta (L0.ψ beta) t p) ∂P1 :=
      fun B hB => withDensity_apply _ hB
    rw [← hν1_apply A hAm]
    refine MeasurableSpace.induction_on_inter
      (m := cadlagFiltr t)
      (C := fun B _ => Q1 B = ν1 B)
      (cadlagFiltr_eq_generateFrom_cylinders t)
      (isPiSystem_cadlagCylinders t)
      ?_ ?_ ?_ ?_ A hA
    · simp
    · rintro B ⟨I, hI, E, hE, rfl⟩
      have hBm : MeasurableSet ((fun p : CadlagSNL => I.restrict p.val) ⁻¹' E) :=
        ((Finset.measurable_restrict I).comp measurable_cadlagVal) hE
      have hCyl_measF : MeasurableSet[PerfCorrMSQ.natFiltr evalF t] (I.restrict ⁻¹' E) := by
        rw [natFiltr_eval_eq_generateFrom_cylinders t]
        exact MeasurableSpace.measurableSet_generateFrom ⟨I, hI, E, hE, rfl⟩
      have hQ1_eq : Q1 ((fun p : CadlagSNL => I.restrict p.val) ⁻¹' E) = μQ (I.restrict ⁻¹' E) := by
        dsimp only [Q1]
        rw [Measure.map_apply measurable_cadlagModify hBm]
        have hae_fin : ∀ᵐ f ∂μQ, ∀ s ∈ I, (cadlagModify f).val s = f s :=
          ae_ball_iff I.countable_toSet |>.mpr fun s _ => hμQ_ae_eq s
        refine measure_congr ?_
        filter_upwards [hae_fin] with f hf
        change ((I.restrict (cadlagModify f).val) ∈ E) = (I.restrict f ∈ E)
        have hfun : I.restrict (cadlagModify f).val = I.restrict f := by
          ext s; exact hf s.1 s.2
        rw [hfun]
      have hrm : Measurable (I.restrict (π := fun _ : NNReal => ℝ)) :=
        Finset.measurable_restrict (X := fun _ : NNReal => ℝ) I
      have hν1_eq : ν1 ((fun p : CadlagSNL => I.restrict p.val) ⁻¹' E) =
          ∫⁻ f in I.restrict ⁻¹' E, ENNReal.ofReal (esscherDensity evalF beta (L.ψ beta) t f) ∂μP := by
        rw [hν1_apply _ hBm, hμP_eq,
          setLIntegral_map (hrm hE) (hEssF_meas t) measurable_cadlagVal]
        rfl
      rw [hQ1_eq, hν1_eq, hμQ_natFiltr t _ hCyl_measF]
    · intro B hBm hEq
      have hB1 : MeasurableSet B := cadlagFiltr.le t B hBm
      rw [measure_compl hB1 (measure_ne_top Q1 B),
        measure_compl hB1 (measure_ne_top ν1 B),
        measure_univ, measure_univ, hEq]
    · intro g hdisj hgm hEq
      have hg1 : ∀ i, MeasurableSet (g i) := fun i => cadlagFiltr.le t _ (hgm i)
      rw [measure_iUnion hdisj hg1, measure_iUnion hdisj hg1]
      exact tsum_congr hEq
