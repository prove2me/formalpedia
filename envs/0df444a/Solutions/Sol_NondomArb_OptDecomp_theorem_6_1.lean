-- Prove2me | solution 1 for NondomArb.OptDecomp.theorem_6_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:37:48.578079+00:00
-- url     : https://prove2.me/submissions/94604ca1-116a-468d-aa9e-cb89806f584c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_OptDecomp_Model
import Definitions.Def_NondomArb_OptDecomp_Process
import Theorems.Thm_NondomArb_OptDecomp_eq_6_1
import Theorems.Thm_NondomArb_OptDecomp_lemma_4_10
import Theorems.Thm_NondomArb_OptDecomp_lemma_4_6

open MeasureTheory ProbabilityTheory BertsekasShreve.AnalyticSelection

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace OD61Aux

open NondomArb.Superhedge (pre law IsUMeasurable)

variable {Ω₁ : Type*} [MeasurableSpace Ω₁]

/-- universal measurability, AE form -/
def UM {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (f : X → Y) : Prop :=
  ∀ p : Measure X, IsProbabilityMeasure p → AEMeasurable f p

lemma isUMeasurable_iff_nullMeasurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) :
    IsUMeasurable f ↔ ∀ p : Measure X, IsProbabilityMeasure p → NullMeasurable f p := by
  unfold IsUMeasurable IsUniversallyMeasurableFun IsUniversallyMeasurable
  constructor
  · rintro ⟨-, h⟩ p hp B hB
    have := h B hB p hp
    have e : (Subtype.val '' ((fun x : (Set.univ : Set X) => f x) ⁻¹' B)) = f ⁻¹' B := by
      ext x; simp
    rwa [e] at this
  · intro h
    refine ⟨fun p _ => nullMeasurableSet_univ, fun B hB p hp => ?_⟩
    have e : (Subtype.val '' ((fun x : (Set.univ : Set X) => f x) ⁻¹' B)) = f ⁻¹' B := by
      ext x; simp
    rw [e]; exact h p hp hB

lemma UM_of_isUMeasurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] {f : X → Y} (hf : IsUMeasurable f) : UM f :=
  fun p hp => ((isUMeasurable_iff_nullMeasurable f).1 hf p hp).aemeasurable

lemma isUMeasurable_of_UM {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : UM f) : IsUMeasurable f :=
  (isUMeasurable_iff_nullMeasurable f).2 fun p hp => (hf p hp).nullMeasurable

lemma UM.comp {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {f : Y → Z} {g : X → Y} (hf : UM f) (hg : Measurable g) : UM (f ∘ g) := by
  intro p hp
  haveI : IsProbabilityMeasure (p.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  exact (hf _ this).comp_measurable hg

lemma UM_of_measurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : Measurable f) : UM f := fun _ _ => hf.aemeasurable

lemma measurable_pre {T : ℕ} (t : ℕ) (h : t ≤ T) :
    Measurable (fun ω : Fin T → Ω₁ => pre ω t h) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

lemma pre_pre {T : ℕ} (ω : Fin T → Ω₁) (s t : ℕ) (hs : s ≤ T) (ht : t ≤ s) :
    pre (pre ω s hs) t ht = pre ω t (ht.trans hs) := rfl

lemma pre_self {T : ℕ} (ω : Fin T → Ω₁) : pre ω T le_rfl = ω := rfl

lemma pre_snoc {t : ℕ} (ω : Fin t → Ω₁) (x : Ω₁) :
    pre (Fin.snoc (α := fun _ => Ω₁) ω x) t (Nat.le_succ t) = ω := by
  funext i
  simp only [pre]
  have : (Fin.castLE (Nat.le_succ t) i) = Fin.castSucc i := rfl
  rw [this, Fin.snoc_castSucc]

lemma measurable_snoc (t : ℕ) :
    Measurable (fun p : (Fin t → Ω₁) × Ω₁ => Fin.snoc (α := fun _ => Ω₁) p.1 p.2) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]; exact measurable_snd
  · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply j).comp measurable_fst

/-- the measurable equivalence `Ω_t × Ω₁ ≃ Ω_{t+1}` -/
def snocEquiv (t : ℕ) : ((Fin t → Ω₁) × Ω₁) ≃ᵐ (Fin (t + 1) → Ω₁) where
  toFun p := Fin.snoc (α := fun _ => Ω₁) p.1 p.2
  invFun ω := (Fin.init ω, ω (Fin.last t))
  left_inv p := by simp
  right_inv ω := by simp
  measurable_toFun := measurable_snoc t
  measurable_invFun := by
    refine Measurable.prodMk ?_ (measurable_pi_apply _)
    exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

lemma snocEquiv_apply (t : ℕ) (p : (Fin t → Ω₁) × Ω₁) :
    snocEquiv t p = Fin.snoc (α := fun _ => Ω₁) p.1 p.2 := rfl

lemma law_succ (κ : (t : ℕ) → Kernel (Fin t → Ω₁) Ω₁) (t : ℕ) :
    law κ (t + 1) = ((law κ t) ⊗ₘ (κ t)).map (snocEquiv t) := rfl

lemma isProb_law (κ : (t : ℕ) → Kernel (Fin t → Ω₁) Ω₁) :
    ∀ s, (∀ u < s, IsMarkovKernel (κ u)) → IsProbabilityMeasure (law κ s)
  | 0, _ => by simp only [law]; infer_instance
  | s + 1, h => by
    haveI := isProb_law κ s (fun u hu => h u (by omega))
    haveI := h s (by omega)
    rw [law_succ]
    exact Measure.isProbabilityMeasure_map (snocEquiv (Ω₁ := Ω₁) s).measurable.aemeasurable

lemma map_pre_law (κ : (t : ℕ) → Kernel (Fin t → Ω₁) Ω₁) (t : ℕ) :
    ∀ s (hts : t ≤ s), (∀ u < s, IsMarkovKernel (κ u)) →
      (law κ s).map (fun ω => pre ω t hts) = law κ t := by
  intro s
  induction s with
  | zero =>
    intro hts _
    obtain rfl : t = 0 := by omega
    exact Measure.map_id
  | succ s ih =>
    intro hts h
    rcases Nat.lt_or_ge s t with hlt | hle
    · obtain rfl : t = s + 1 := by omega
      exact Measure.map_id
    · haveI := isProb_law κ s (fun u hu => h u (by omega))
      haveI := h s (by omega)
      rw [law_succ, Measure.map_map (measurable_pre _ _) (snocEquiv s).measurable]
      have e : ((fun ω : Fin (s+1) → Ω₁ => pre ω t hts) ∘ (snocEquiv s)) =
          (fun ω => pre ω t hle) ∘ Prod.fst := by
        funext p
        simp only [Function.comp, snocEquiv_apply]
        rw [show pre (Fin.snoc (α := fun _ => Ω₁) p.1 p.2) t hts =
          pre (pre (Fin.snoc (α := fun _ => Ω₁) p.1 p.2) s (Nat.le_succ s)) t hle from rfl, pre_snoc]
      rw [e, ← Measure.map_map (measurable_pre _ _) measurable_fst]
      rw [← Measure.fst, Measure.fst_compProd]
      exact ih hle (fun u hu => h u (by omega))


lemma compProd_null {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]
    (P : Measure Ω) (π : Ω → X) (hπ : Measurable π) [SFinite (P.map π)]
    (κ : Kernel X Y) [IsSFiniteKernel κ] (D : Set (X × Y))
    (hD : NullMeasurableSet D ((P.map π) ⊗ₘ κ))
    (Bad : Set X) (hBad : P (π ⁻¹' Bad) = 0)
    (hgood : ∀ ω ∉ Bad, κ ω (Prod.mk ω ⁻¹' D) = 0) :
    ((P.map π) ⊗ₘ κ) D = 0 := by
  set ν := P.map π
  obtain ⟨D', hDD', hD'm, hD'eq⟩ := hD.exists_measurable_superset_ae_eq
  set N' := toMeasurable (ν ⊗ₘ κ) (D' \ D)
  have hN0 : (ν ⊗ₘ κ) (D' \ D) = 0 := (ae_eq_set.1 hD'eq).1
  have hN'm : MeasurableSet N' := measurableSet_toMeasurable _ _
  have hN'0 : (ν ⊗ₘ κ) N' = 0 := by rw [measure_toMeasurable]; exact hN0
  rw [Measure.compProd_apply hN'm] at hN'0
  have hh := (lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hN'm)).1 hN'0
  rw [← measure_congr hD'eq, Measure.compProd_apply hD'm]
  apply (lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hD'm)).2
  rw [Filter.EventuallyEq, ae_iff]
  have hEm : MeasurableSet {ω | ¬ (κ ω (Prod.mk ω ⁻¹' D')) = (0 : X → ENNReal) ω} :=
    (Kernel.measurable_kernel_prodMk_left hD'm) (measurableSet_singleton 0).compl
  have hFm : MeasurableSet {ω | ¬ (κ ω (Prod.mk ω ⁻¹' N')) = (0 : X → ENNReal) ω} :=
    (Kernel.measurable_kernel_prodMk_left hN'm) (measurableSet_singleton 0).compl
  rw [Measure.map_apply hπ hEm]
  have hsub : π ⁻¹' {ω | ¬ (κ ω (Prod.mk ω ⁻¹' D')) = (0 : X → ENNReal) ω} ⊆
      π ⁻¹' Bad ∪ π ⁻¹' {ω | ¬ (κ ω (Prod.mk ω ⁻¹' N')) = (0 : X → ENNReal) ω} := by
    intro x hx
    by_contra hc
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, not_or, not_not,
      Pi.zero_apply] at hc hx
    apply hx
    refine measure_mono_null (t := Prod.mk (π x) ⁻¹' D ∪ Prod.mk (π x) ⁻¹' N') ?_ ?_
    · intro y hy
      by_cases hyD : (π x, y) ∈ D
      · exact Or.inl hyD
      · exact Or.inr (subset_toMeasurable _ _ ⟨hy, hyD⟩)
    · exact measure_union_null (hgood _ hc.1) hc.2
  refine measure_mono_null hsub (measure_union_null hBad ?_)
  rw [← Measure.map_apply hπ hFm]
  rw [Filter.EventuallyEq, ae_iff] at hh
  exact hh


lemma aemeasurable_dotProduct {X : Type*} [MeasurableSpace X] {μ : Measure X} {d : ℕ}
    {u v : X → Fin d → ℝ} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ) :
    AEMeasurable (fun x => u x ⬝ᵥ v x) μ := by
  have hm : Measurable (fun q : (Fin d → ℝ) × (Fin d → ℝ) => q.1 ⬝ᵥ q.2) := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd))
  exact hm.comp_aemeasurable (hu.prodMk hv)

lemma integral_test_zero {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (π : Ω → X) (hπ : Measurable π)
    (f : Ω → ℝ) (hf : Integrable f Q)
    (hzero : ∀ B, MeasurableSet B → ∫ ω in π ⁻¹' B, f ω ∂Q = 0)
    (g : X → ℝ) (hg : Measurable g) (c : ℝ) (hgc : ∀ x, ‖g x‖ ≤ c) :
    ∫ ω, g (π ω) * f ω ∂Q = 0 := by
  have hm : MeasurableSpace.comap π mX ≤ mΩ := hπ.comap_le
  haveI : IsFiniteMeasure (Q.trim hm) := isFiniteMeasure_trim hm
  have hce : (0 : Ω → ℝ) =ᵐ[Q] Q[f|MeasurableSpace.comap π mX] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun s _ _ => integrableOn_zero)
      (fun s hs _ => ?_) aestronglyMeasurable_zero
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
    simp [hzero B hB]
  have hGm : StronglyMeasurable[MeasurableSpace.comap π mX] (fun ω => g (π ω)) :=
    (hg.comp (comap_measurable π)).stronglyMeasurable
  have hint : Integrable ((fun ω => g (π ω)) * f) Q :=
    hf.bdd_mul (hg.comp hπ).aestronglyMeasurable (ae_of_all _ (fun x => hgc (π x)))
  have h1 := condExp_mul_of_stronglyMeasurable_left (m := MeasurableSpace.comap π mX) hGm hint hf
  calc ∫ ω, g (π ω) * f ω ∂Q = ∫ ω, ((fun ω => g (π ω)) * f) ω ∂Q := rfl
    _ = ∫ ω, Q[(fun ω => g (π ω)) * f|MeasurableSpace.comap π mX] ω ∂Q :=
        (integral_condExp hm).symm
    _ = ∫ ω, ((fun ω => g (π ω)) * Q[f|MeasurableSpace.comap π mX]) ω ∂Q := integral_congr_ae h1
    _ = ∫ ω, (0 : Ω → ℝ) ω ∂Q := by
        refine integral_congr_ae ?_
        filter_upwards [hce] with ω hω
        simp [← hω]
    _ = 0 := by simp

section Market
open NondomArb.OptDecomp
variable [TopologicalSpace Ω₁] {T d : ℕ}

lemma step_qs (M : Market Ω₁ T d 0) (hS : ∀ t ≤ T, Measurable (M.S t))
    (V : (t : ℕ) → (Fin t → Ω₁) → ℝ) (hV : M.Adapted V) (t : ℕ) (ht : t < T)
    (y : (Fin t → Ω₁) → (Fin d → ℝ)) (hy : IsUMeasurable y)
    (hpolar : M.IsPolar ((fun ω => pre ω t ht.le) ⁻¹' M.badSet t))
    (h61 : M.QS (fun ω =>
      M.condSup t (fun p => ((V (t + 1) (Fin.snoc (α := fun _ => Ω₁) p.1 p.2) : ℝ) : EReal))
        (pre ω t ht.le) ≤ ((V t (pre ω t ht.le) : ℝ) : EReal)))
    (h410 : ∀ ω : Fin t → Ω₁, M.LocalNA t ω →
          (∀ P ∈ M.Pt t ω, ∀ᵐ x ∂(P : Measure Ω₁),
            ⊥ < ((V (t + 1) (Fin.snoc (α := fun _ => Ω₁) ω x) : ℝ) : EReal)) →
          ∀ P ∈ M.Pt t ω, ∀ᵐ x ∂(P : Measure Ω₁),
            ((V (t + 1) (Fin.snoc (α := fun _ => Ω₁) ω x) : ℝ) : EReal) ≤
              M.condSup t (fun p => ((V (t + 1) (Fin.snoc (α := fun _ => Ω₁) p.1 p.2) : ℝ) : EReal)) ω
                + ((y ω ⬝ᵥ M.incr t ω x : ℝ) : EReal)) :
    M.QS (fun ω => V (t + 1) (pre ω (t + 1) ht) ≤ V t (pre ω t ht.le) +
      y (pre ω t ht.le) ⬝ᵥ (M.S (t + 1) (pre ω (t + 1) ht) - M.S t (pre ω t ht.le))) := by
  intro P hP
  obtain ⟨κ, hκ, hκP, rfl⟩ := hP
  haveI hκt : IsMarkovKernel (κ t) := hκ t ht
  haveI : IsProbabilityMeasure (law κ t) := isProb_law κ t (fun u hu => hκ u (by omega))
  haveI : IsProbabilityMeasure (law κ T) := isProb_law κ T hκ
  have hmap_t : (law κ T).map (fun ω => pre ω t ht.le) = law κ t := map_pre_law κ t T ht.le hκ
  have hmap_t1 : (law κ T).map (fun ω => pre ω (t + 1) ht) = law κ (t + 1) :=
    map_pre_law κ (t + 1) T ht hκ
  set f := (fun p : (Fin t → Ω₁) × Ω₁ =>
    ((V (t + 1) (Fin.snoc (α := fun _ => Ω₁) p.1 p.2) : ℝ) : EReal))
  set D : Set ((Fin t → Ω₁) × Ω₁) := {p | V t p.1 + y p.1 ⬝ᵥ M.incr t p.1 p.2 <
      V (t + 1) (Fin.snoc (α := fun _ => Ω₁) p.1 p.2)} with hDdef
  haveI : IsProbabilityMeasure ((law κ t) ⊗ₘ (κ t)) := inferInstance
  have hD : NullMeasurableSet D ((law κ t) ⊗ₘ (κ t)) := by
    have h1 : AEMeasurable (fun p : (Fin t → Ω₁) × Ω₁ =>
        V (t + 1) (Fin.snoc (α := fun _ => Ω₁) p.1 p.2)) ((law κ t) ⊗ₘ (κ t)) :=
      (UM.comp (UM_of_isUMeasurable (hV (t + 1) ht)) (measurable_snoc t)) _ inferInstance
    have h2 : AEMeasurable (fun p : (Fin t → Ω₁) × Ω₁ => V t p.1) ((law κ t) ⊗ₘ (κ t)) :=
      (UM.comp (UM_of_isUMeasurable (hV t ht.le)) measurable_fst) _ inferInstance
    have h3 : AEMeasurable (fun p : (Fin t → Ω₁) × Ω₁ => y p.1) ((law κ t) ⊗ₘ (κ t)) :=
      (UM.comp (UM_of_isUMeasurable hy) measurable_fst) _ inferInstance
    have h4 : AEMeasurable (fun p : (Fin t → Ω₁) × Ω₁ => M.incr t p.1 p.2) ((law κ t) ⊗ₘ (κ t)) := by
      refine Measurable.aemeasurable ?_
      exact ((hS (t + 1) ht).comp (measurable_snoc t)).sub ((hS t ht.le).comp measurable_fst)
    exact nullMeasurableSet_lt (h2.add (aemeasurable_dotProduct h3 h4)) h1
  set Bad : Set (Fin t → Ω₁) := M.badSet t ∪
    {ω | ¬ (M.condSup t f ω ≤ ((V t ω : ℝ) : EReal))} ∪
    {ω | ¬ ∃ R ∈ M.Pt t ω, (R : Measure Ω₁) = κ t ω}
  have hBad : (law κ T) ((fun ω => pre ω t ht.le) ⁻¹' Bad) = 0 := by
    simp only [Bad, Set.preimage_union]
    refine measure_union_null (measure_union_null ?_ ?_) ?_
    · exact hpolar _ ⟨κ, hκ, hκP, rfl⟩
    · exact ae_iff.1 (h61 _ ⟨κ, hκ, hκP, rfl⟩)
    · refine nonpos_iff_eq_zero.1 ?_
      refine (Measure.le_map_apply (measurable_pre t ht.le).aemeasurable _).trans ?_
      rw [hmap_t]
      exact (ae_iff.1 (hκP t ht)).le
  have hgood : ∀ ω ∉ Bad, κ t ω (Prod.mk ω ⁻¹' D) = 0 := by
    intro ω hω
    simp only [Bad, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, NondomArb.OptDecomp.Market.badSet] at hω
    obtain ⟨⟨hNA, hcs⟩, R, hR, hRκ⟩ := hω
    have := h410 ω hNA (fun _ _ => ae_of_all _ (fun x => EReal.bot_lt_coe _)) R hR
    rw [hRκ] at this
    have h' : ∀ᵐ x ∂(κ t ω), x ∉ Prod.mk ω ⁻¹' D := by
      filter_upwards [this] with x hx
      simp only [Set.mem_preimage, hDdef, Set.mem_ofPred_eq, not_lt]
      have h2 : ((V (t + 1) (Fin.snoc (α := fun _ => Ω₁) ω x) : ℝ) : EReal) ≤
          ((V t ω + y ω ⬝ᵥ M.incr t ω x : ℝ) : EReal) := by
        rw [EReal.coe_add]
        exact hx.trans (add_le_add_left hcs _)
      exact_mod_cast h2
    exact measure_mono_null (fun x hx => not_not.2 hx) (ae_iff.1 h')
  haveI : SFinite ((law κ T).map (fun ω => pre ω t ht.le)) := by rw [hmap_t]; infer_instance
  have hD0 : ((law κ t) ⊗ₘ (κ t)) D = 0 := by
    have := compProd_null (law κ T) (fun ω => pre ω t ht.le) (measurable_pre t ht.le) (κ t) D
      (by rw [hmap_t]; exact hD) Bad hBad hgood
    rwa [hmap_t] at this
  refine ae_iff.2 ?_
  refine nonpos_iff_eq_zero.1 ?_
  set D₂ : Set (Fin (t + 1) → Ω₁) := {ω' | ¬ (V (t + 1) ω' ≤ V t (pre ω' t (Nat.le_succ t)) +
      y (pre ω' t (Nat.le_succ t)) ⬝ᵥ (M.S (t + 1) ω' - M.S t (pre ω' t (Nat.le_succ t))))}
  refine (Measure.le_map_apply (measurable_pre (t + 1) ht).aemeasurable D₂).trans ?_
  rw [hmap_t1, law_succ, MeasurableEquiv.map_apply]
  have e : (snocEquiv t) ⁻¹' D₂ = D := by
    ext p
    simp only [D₂, hDdef, Set.mem_preimage, snocEquiv_apply, Set.mem_ofPred_eq, not_le, pre_snoc,
      NondomArb.OptDecomp.Market.incr]
  rw [e, hD0]


lemma gainAt_succ (M : Market Ω₁ T d 0) (H : (u : ℕ) → (Fin u → Ω₁) → (Fin d → ℝ)) (t : ℕ)
    (ω : Fin (t + 1) → Ω₁) :
    M.gainAt H (t + 1) ω = M.gainAt H t (pre ω t (Nat.le_succ t)) +
      H t (pre ω t (Nat.le_succ t)) ⬝ᵥ (M.S (t + 1) ω - M.S t (pre ω t (Nat.le_succ t))) := by
  simp only [NondomArb.OptDecomp.Market.gainAt]
  rw [Fin.sum_univ_castSucc]
  rfl

lemma gainAt_succ' (M : Market Ω₁ T d 0) (H : (u : ℕ) → (Fin u → Ω₁) → (Fin d → ℝ)) (t : ℕ)
    (ht : t < T) (ω : Fin T → Ω₁) :
    M.gainAt H (t + 1) (pre ω (t + 1) ht) = M.gainAt H t (pre ω t ht.le) +
      H t (pre ω t ht.le) ⬝ᵥ (M.S (t + 1) (pre ω (t + 1) ht) - M.S t (pre ω t ht.le)) :=
  gainAt_succ M H t (pre ω (t + 1) ht)

lemma gainAt_zero (M : Market Ω₁ T d 0) (H : (u : ℕ) → (Fin u → Ω₁) → (Fin d → ℝ))
    (ω : Fin 0 → Ω₁) : M.gainAt H 0 ω = 0 := by
  simp [NondomArb.OptDecomp.Market.gainAt]

/-- running maximum, started at `0` -/
noncomputable def runMax (K0 : (t : ℕ) → (Fin t → Ω₁) → ℝ) : (t : ℕ) → (Fin t → Ω₁) → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun ω => max (runMax K0 t (pre ω t (Nat.le_succ t))) (K0 (t + 1) ω)

lemma UM_gainAt (M : Market Ω₁ T d 0) (hS : ∀ t ≤ T, Measurable (M.S t))
    (H : (u : ℕ) → (Fin u → Ω₁) → (Fin d → ℝ)) (hH : M.Admissible H) (t : ℕ) (ht : t ≤ T) :
    UM (M.gainAt H t) := by
  intro p hp
  have := Finset.aemeasurable_sum (μ := p) (Finset.univ : Finset (Fin t))
    (f := fun (u : Fin t) (ω : Fin t → Ω₁) => H (u : ℕ) (pre ω u u.isLt.le) ⬝ᵥ
      (M.S ((u : ℕ) + 1) (pre ω ((u : ℕ) + 1) u.isLt) - M.S (u : ℕ) (pre ω u u.isLt.le)))
    (fun u _ => by
      refine aemeasurable_dotProduct ?_ ?_
      · exact (UM.comp (UM_of_isUMeasurable (hH u (by omega))) (measurable_pre _ _)) p hp
      · exact (((hS _ (by omega)).comp (measurable_pre _ _)).sub
          ((hS _ (by omega)).comp (measurable_pre _ _))).aemeasurable)
  convert this using 1
  funext ω
  simp [Finset.sum_apply, NondomArb.OptDecomp.Market.gainAt]

lemma forward_construct (M : Market Ω₁ T d 0) (hS : ∀ t ≤ T, Measurable (M.S t))
    (V : (t : ℕ) → (Fin t → Ω₁) → ℝ) (hV : M.Adapted V)
    (y : (t : ℕ) → (Fin t → Ω₁) → (Fin d → ℝ)) (hy : ∀ t < T, IsUMeasurable (y t))
    (hstep : ∀ t (ht : t < T), M.QS (fun ω => V (t + 1) (pre ω (t + 1) ht) ≤ V t (pre ω t ht.le) +
      y t (pre ω t ht.le) ⬝ᵥ (M.S (t + 1) (pre ω (t + 1) ht) - M.S t (pre ω t ht.le)))) :
    ∃ H, M.Admissible H ∧ ∃ K : (t : ℕ) → (Fin t → Ω₁) → ℝ, M.IsAdaptedIncreasing K ∧
        (∀ ω, K 0 ω = 0) ∧
        ∀ t (ht : t ≤ T), M.QS (fun ω =>
          V t (pre ω t ht) = V 0 (pre ω 0 (Nat.zero_le T)) + M.gainAt H t (pre ω t ht)
            - K t (pre ω t ht)) := by
  set K0 : (t : ℕ) → (Fin t → Ω₁) → ℝ := fun t ω =>
    V 0 (pre ω 0 (Nat.zero_le t)) + M.gainAt y t ω - V t ω with hK0
  refine ⟨y, hy, runMax K0, ⟨?_, fun t ht ω => le_max_left _ _⟩, fun ω => rfl, ?_⟩
  · -- adaptedness
    have hK0UM : ∀ t ≤ T, UM (K0 t) := by
      intro t ht p hp
      refine AEMeasurable.sub (AEMeasurable.add ?_ ?_) ?_
      · exact (UM.comp (UM_of_isUMeasurable (hV 0 (Nat.zero_le T))) (measurable_pre _ _)) p hp
      · exact UM_gainAt M hS y hy t ht p hp
      · exact UM_of_isUMeasurable (hV t ht) p hp
    have : ∀ t ≤ T, UM (runMax K0 t) := by
      intro t
      induction t with
      | zero => intro _; exact UM_of_measurable measurable_const
      | succ t ih =>
        intro ht p hp
        exact AEMeasurable.max ((UM.comp (ih (by omega)) (measurable_pre _ _)) p hp)
          (hK0UM (t + 1) ht p hp)
    exact fun t ht => isUMeasurable_of_UM (this t ht)
  · intro t ht P hP
    have hall : ∀ᵐ ω ∂P, ∀ u : Fin T, V (u + 1) (pre ω (u + 1) u.isLt) ≤ V u (pre ω u u.isLt.le) +
        y u (pre ω u u.isLt.le) ⬝ᵥ (M.S (u + 1) (pre ω (u + 1) u.isLt) - M.S u (pre ω u u.isLt.le)) :=
      ae_all_iff.2 (fun u => hstep u u.isLt P hP)
    filter_upwards [hall] with ω hω
    have key : ∀ s (hs : s ≤ T), runMax K0 s (pre ω s hs) = K0 s (pre ω s hs) := by
      intro s
      induction s with
      | zero =>
        intro hs
        simp only [runMax, hK0, gainAt_zero]
        exact (by ring : (0:ℝ) = V 0 (pre ω 0 hs) + 0 - V 0 (pre ω 0 hs))
      | succ s ih =>
        intro hs
        have h1 := ih (by omega)
        show max (runMax K0 s (pre ω s (by omega))) (K0 (s + 1) (pre ω (s + 1) hs)) = _
        rw [h1]
        apply max_eq_right
        have h2 := hω ⟨s, hs⟩
        have h3 := gainAt_succ' M y s hs ω
        simp only [hK0]
        have e0 : V 0 (pre (pre ω (s + 1) hs) 0 (Nat.zero_le (s + 1))) =
            V 0 (pre (pre ω s (by omega)) 0 (Nat.zero_le s)) := rfl
        rw [e0, h3]
        simp only at h2
        linarith
    rw [key t ht]
    simp only [hK0]
    have e0 : V 0 (pre (pre ω t ht) 0 (Nat.zero_le t)) = V 0 (pre ω 0 (Nat.zero_le T)) := rfl
    rw [e0]
    ring


lemma backward (M : Market Ω₁ T d 0) (V : (t : ℕ) → (Fin t → Ω₁) → ℝ)
    (hVint : ∀ Q ∈ M.MartMeasures, ∀ t (ht1 : 1 ≤ t) (ht : t ≤ T),
      Integrable (fun ω => V t (pre ω t ht)) Q)
    (H : (u : ℕ) → (Fin u → Ω₁) → (Fin d → ℝ)) (hH : M.Admissible H)
    (K : (t : ℕ) → (Fin t → Ω₁) → ℝ) (hK : M.IsAdaptedIncreasing K)
    (hrep : ∀ t (ht : t ≤ T), M.QS (fun ω =>
          V t (pre ω t ht) = V 0 (pre ω 0 (Nat.zero_le T)) + M.gainAt H t (pre ω t ht)
            - K t (pre ω t ht))) :
    ∀ Q ∈ M.MartMeasures, M.IsSupermartingale V Q := by
  intro Q hQ
  obtain ⟨hQprob, ⟨P, hP, hQP⟩, ⟨hSint, hmart⟩, -⟩ := hQ
  haveI := hQprob
  have hVint' : ∀ t (ht : t ≤ T), Integrable (fun ω => V t (pre ω t ht)) Q := by
    intro t ht
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · have : (fun ω : Fin T → Ω₁ => V 0 (pre ω 0 ht)) = fun _ => V 0 (fun i => i.elim0) := by
        funext ω; congr 1; funext i; exact i.elim0
      rw [this]; exact integrable_const _
    · exact hVint Q ⟨hQprob, ⟨P, hP, hQP⟩, ⟨hSint, hmart⟩, fun i => i.elim0⟩ t hpos ht
  refine ⟨hVint', fun t ht B hB => ?_⟩
  set C := (fun ω : Fin T → Ω₁ => pre ω t ht.le) ⁻¹' B with hCdef
  have hC : MeasurableSet C := measurable_pre t ht.le hB
  set Dv : (Fin T → Ω₁) → ℝ := fun ω => V (t + 1) (pre ω (t + 1) ht) - V t (pre ω t ht.le)
    with hDvdef
  have hDv : Integrable Dv Q := (hVint' _ ht).sub (hVint' _ ht.le)
  set dS : Fin d → (Fin T → Ω₁) → ℝ := fun i ω =>
    M.S (t + 1) (pre ω (t + 1) ht) i - M.S t (pre ω t ht.le) i with hdSdef
  have hdS : ∀ i, Integrable (dS i) Q := fun i =>
    (hSint ⟨t + 1, by omega⟩ i).sub (hSint ⟨t, by omega⟩ i)
  have hmart' : ∀ i B', MeasurableSet B' →
      ∫ ω in (fun ω : Fin T → Ω₁ => pre ω t ht.le) ⁻¹' B', dS i ω ∂Q = 0 :=
    fun i B' hB' => hmart ⟨t, ht⟩ i B' hB'
  haveI : IsProbabilityMeasure (Q.map (fun ω => pre ω t ht.le)) :=
    Measure.isProbabilityMeasure_map (measurable_pre t ht.le).aemeasurable
  have hHae : AEMeasurable (H t) (Q.map (fun ω => pre ω t ht.le)) :=
    UM_of_isUMeasurable (hH t ht) _ inferInstance
  set h' := hHae.mk (H t)
  have hh'm : Measurable h' := hHae.measurable_mk
  have hHeq : ∀ᵐ ω ∂Q, H t (pre ω t ht.le) = h' (pre ω t ht.le) :=
    ae_of_ae_map (measurable_pre t ht.le).aemeasurable hHae.ae_eq_mk
  have hineq : ∀ᵐ ω ∂Q, Dv ω ≤ ∑ i, h' (pre ω t ht.le) i * dS i ω := by
    filter_upwards [hQP.ae_le (hrep _ ht P hP), hQP.ae_le (hrep _ ht.le P hP), hHeq]
      with ω h1 h2 h3
    have h4 := gainAt_succ' M H t ht ω
    have h5 : K t (pre ω t ht.le) ≤ K (t + 1) (pre ω (t + 1) ht) := hK.2 t ht (pre ω (t + 1) ht)
    have h6 : ∑ i, h' (pre ω t ht.le) i * dS i ω =
        H t (pre ω t ht.le) ⬝ᵥ (M.S (t + 1) (pre ω (t + 1) ht) - M.S t (pre ω t ht.le)) := by
      rw [h3]; rfl
    rw [h6]
    simp only [hDvdef]
    linarith
  set Bn : ℕ → Set (Fin t → Ω₁) := fun n => B ∩ {x | ‖h' x‖ ≤ n} with hBndef
  have hBn : ∀ n, MeasurableSet (Bn n) := fun n =>
    hB.inter (measurableSet_le hh'm.norm measurable_const)
  have hbd : ∀ n i x, ‖(Bn n).indicator (fun x => h' x i) x‖ ≤ n := by
    intro n i x
    by_cases hx : x ∈ Bn n
    · rw [Set.indicator_of_mem hx]
      exact (norm_le_pi_norm (h' x) i).trans hx.2
    · rw [Set.indicator_of_notMem hx]; simp
  set Φ : ℕ → (Fin T → Ω₁) → ℝ := fun n ω =>
    ∑ i, (Bn n).indicator (fun x => h' x i) (pre ω t ht.le) * dS i ω with hΦdef
  have hgm : ∀ n i, Measurable ((Bn n).indicator (fun x => h' x i)) := fun n i =>
    ((measurable_pi_apply i).comp hh'm).indicator (hBn n)
  have hΦint : ∀ n, Integrable (Φ n) Q := by
    intro n
    refine integrable_finsetSum _ (fun i _ => ?_)
    exact (hdS i).bdd_mul (((hgm n i).comp (measurable_pre t ht.le)).aestronglyMeasurable)
      (ae_of_all _ (fun ω => hbd n i _))
  have hΦ0 : ∀ n, ∫ ω, Φ n ω ∂Q = 0 := by
    intro n
    simp only [hΦdef]
    rw [integral_finsetSum (f := fun i ω => (Bn n).indicator (fun x => h' x i) (pre ω t ht.le) * dS i ω)
      _ (fun i _ => (hdS i).bdd_mul
      (((hgm n i).comp (measurable_pre t ht.le)).aestronglyMeasurable)
      (ae_of_all _ (fun ω => hbd n i _)))]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    exact integral_test_zero Q (fun ω => pre ω t ht.le) (measurable_pre t ht.le) (dS i) (hdS i)
      (hmart' i) _ (hgm n i) n (hbd n i)
  set Cn : ℕ → Set (Fin T → Ω₁) := fun n => (fun ω => pre ω t ht.le) ⁻¹' (Bn n) with hCndef
  have hCn : ∀ n, MeasurableSet (Cn n) := fun n => measurable_pre t ht.le (hBn n)
  have hle : ∀ n, ∫ ω, (Cn n).indicator Dv ω ∂Q ≤ 0 := by
    intro n
    rw [← hΦ0 n]
    refine integral_mono_ae (hDv.indicator (hCn n)) (hΦint n) ?_
    filter_upwards [hineq] with ω hω
    by_cases hω' : pre ω t ht.le ∈ Bn n
    · rw [Set.indicator_of_mem (show ω ∈ Cn n from hω')]
      simp only [hΦdef, Set.indicator_of_mem hω']
      exact hω
    · rw [Set.indicator_of_notMem (show ω ∉ Cn n from hω')]
      simp [hΦdef, Set.indicator_of_notMem hω']
  have hlim : Filter.Tendsto (fun n : ℕ => ∫ ω, (Cn n).indicator Dv ω ∂Q) Filter.atTop
      (nhds (∫ ω, C.indicator Dv ω ∂Q)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => ‖Dv ω‖)
      (fun n => (hDv.indicator (hCn n)).aestronglyMeasurable) hDv.norm
      (fun n => ae_of_all _ (fun ω => norm_indicator_le_norm_self _ _)) (ae_of_all _ ?_)
    intro ω
    refine tendsto_const_nhds.congr' ?_
    refine Filter.eventually_atTop.2 ⟨⌈‖h' (pre ω t ht.le)‖⌉₊, fun n hn => ?_⟩
    have hnorm : ‖h' (pre ω t ht.le)‖ ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn)
    by_cases hmem : ω ∈ C
    · have : ω ∈ Cn n := ⟨hmem, hnorm⟩
      show C.indicator Dv ω = (Cn n).indicator Dv ω
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem this]
    · have : ω ∉ Cn n := fun h => hmem h.1
      show C.indicator Dv ω = (Cn n).indicator Dv ω
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem this]
  have hfin : ∫ ω, C.indicator Dv ω ∂Q ≤ 0 := le_of_tendsto' hlim hle
  rw [integral_indicator hC, integral_sub (hVint' _ ht).integrableOn (hVint' _ ht.le).integrableOn]
    at hfin
  linarith


lemma usa_snoc {t : ℕ} (V : (Fin (t + 1) → Ω₁) → ℝ)
    (hV : NondomArb.Superhedge.IsUpperSemianalytic (fun ω : Fin (t + 1) → Ω₁ => ((V ω : ℝ) : EReal))) :
    NondomArb.Superhedge.IsUpperSemianalytic
      (fun p : (Fin t → Ω₁) × Ω₁ => ((V (Fin.snoc (α := fun _ => Ω₁) p.1 p.2) : ℝ) : EReal)) := by
  intro c
  have hcont : Continuous (fun ω : Fin (t + 1) → Ω₁ => (Fin.init ω, ω (Fin.last t))) :=
    Continuous.prodMk (continuous_pi fun i => continuous_apply _) (continuous_apply _)
  have e : {p : (Fin t → Ω₁) × Ω₁ | (c : EReal) < ((V (Fin.snoc (α := fun _ => Ω₁) p.1 p.2) : ℝ) : EReal)} =
      (fun ω : Fin (t + 1) → Ω₁ => (Fin.init ω, ω (Fin.last t))) ''
        {ω | (c : EReal) < ((V ω : ℝ) : EReal)} := by
    ext p
    constructor
    · intro hp
      exact ⟨Fin.snoc (α := fun _ => Ω₁) p.1 p.2, hp, by simp⟩
    · rintro ⟨ω, hω, rfl⟩
      simpa [Fin.snoc_init_self] using hω
  rw [e]
  exact (hV c).image_of_continuous hcont

end Market

end OD61Aux

open OD61Aux in
theorem solution {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁] [MeasurableSpace Ω₁]
    [BorelSpace Ω₁] {T d : ℕ} (M : NondomArb.OptDecomp.Market Ω₁ T d 0) (hM : M.Standing) (hNA : M.NA)
    (V : (t : ℕ) → (Fin t → Ω₁) → ℝ) (hV : M.Adapted V)
    (hVusa : ∀ t, 1 ≤ t → t ≤ T → NondomArb.Superhedge.IsUpperSemianalytic (fun ω : Fin t → Ω₁ => ((V t ω : ℝ) : EReal)))
    (hVint : ∀ Q ∈ M.MartMeasures, ∀ t (ht1 : 1 ≤ t) (ht : t ≤ T),
      Integrable (fun ω => V t (NondomArb.Superhedge.pre ω t ht)) Q) :
    (∀ Q ∈ M.MartMeasures, M.IsSupermartingale V Q) ↔
      ∃ H, M.Admissible H ∧ ∃ K : (t : ℕ) → (Fin t → Ω₁) → ℝ, M.IsAdaptedIncreasing K ∧
        (∀ ω, K 0 ω = 0) ∧
        ∀ t (ht : t ≤ T), M.QS (fun ω =>
          V t (NondomArb.Superhedge.pre ω t ht) = V 0 (NondomArb.Superhedge.pre ω 0 (Nat.zero_le T)) + M.gainAt H t (NondomArb.Superhedge.pre ω t ht)
            - K t (NondomArb.Superhedge.pre ω t ht)) := by
  have hS : ∀ t ≤ T, Measurable (M.S t) := hM.2.2.2.1
  constructor
  · intro hsuper
    have hy : ∀ t, t < T → ∃ y : (Fin t → Ω₁) → (Fin d → ℝ), NondomArb.Superhedge.IsUMeasurable y ∧
        ∀ ω : Fin t → Ω₁, M.LocalNA t ω →
          (∀ P ∈ M.Pt t ω, ∀ᵐ x ∂(P : Measure Ω₁),
            ⊥ < ((V (t + 1) (Fin.snoc (α := fun _ => Ω₁) ω x) : ℝ) : EReal)) →
          ∀ P ∈ M.Pt t ω, ∀ᵐ x ∂(P : Measure Ω₁),
            ((V (t + 1) (Fin.snoc (α := fun _ => Ω₁) ω x) : ℝ) : EReal) ≤
              M.condSup t (fun p => ((V (t + 1) (Fin.snoc (α := fun _ => Ω₁) p.1 p.2) : ℝ) : EReal)) ω
                + ((y ω ⬝ᵥ M.incr t ω x : ℝ) : EReal) := by
      intro t ht
      exact (NondomArb.OptDecomp.lemma_4_10 M hM hNA t ht _
        (usa_snoc (V (t + 1)) (hVusa (t + 1) (by omega) ht))).2
    choose! y hyU hy410 using hy
    refine forward_construct M hS V hV y hyU (fun t ht => ?_)
    exact step_qs M hS V hV t ht (y t) (hyU t ht)
      ((NondomArb.OptDecomp.lemma_4_6 M hM t ht).2 hNA)
      (NondomArb.OptDecomp.eq_6_1 M hM hNA V hV hVusa hVint hsuper t ht)
      (hy410 t ht)
  · rintro ⟨H, hH, K, hK, -, hrep⟩
    exact backward M V hVint H hH K hK hrep

