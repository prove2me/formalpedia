-- Prove2me | solution 1 for MDPFinance.POMDP.theorem_5_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-02T16:09:24.361386+00:00
-- url     : https://prove2.me/submissions/eb75d98c-d503-40ad-a178-43b223e485eb

import Mathlib
import Definitions.Def_MDPFinance_POMDP_Model
import Definitions.Def_MDPFinance_POMDP_Policy
import Definitions.Def_MDPFinance_POMDP_Objective
import Definitions.Def_MDPFinance_POMDP_FilterData
import Definitions.Def_MDPFinance_POMDP_FilteredModel
import Theorems.Thm_MDPFinance_POMDP_theorem_5_3_2

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDP

variable {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY] [MeasurableSpace A]

namespace Sol533

/-- The Structure Assumption (SAN) of Theorem 2.3.8, restated locally for the filtered model
(Bäuerle–Rieder, Definition 2.4.2/Theorem 2.3.8, cited at p. 158, PDF 172; not imported from
chunk `02a` per hard rule 3): classes `IM_n` of value functions and `Δ_n` of decision rules with
(i) `g' ∈ IM_N`; (ii) `v ∈ IM_{n+1} ⟹ T'_n v ∈ IM_n`; (iii) every `v ∈ IM_{n+1}` has a maximizer
of `T'_n v` in `Δ_n`. -/
def SAN (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M)
    (M' : FilteredModel M Fd) (N : ℕ) : Prop :=
  ∃ (IM : ℕ → Set (EX × ProbabilityMeasure EY → EReal))
    (Δ : ℕ → Set (EX × ProbabilityMeasure EY → A)),
    FilteredModel.gprime M ∈ IM N ∧
      (∀ n < N, ∀ v ∈ IM (n + 1), (fun e => FilteredModel.Tprime M Fd M' v e) ∈ IM n) ∧
      ∀ n < N, ∀ v ∈ IM (n + 1), ∃ f ∈ Δ n, Measurable f ∧
        ∀ e : EX × ProbabilityMeasure EY, f e ∈ M.Dx e.1 ∧
          FilteredModel.rprime M e (f e) +
              (M.β : EReal) * erealIntegral (M'.Qprime (e, f e)) v =
            FilteredModel.Tprime M Fd M' v e


/-! ### Generalities on `erealIntegral` -/

lemma erealIntegral_mono {E : Type*} [MeasurableSpace E] (μ : Measure E) {v w : E → EReal}
    (h : ∀ x, v x ≤ w x) : erealIntegral μ v ≤ erealIntegral μ w := by
  unfold erealIntegral
  refine add_le_add ?_ ?_
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono fun x => EReal.toENNReal_le_toENNReal (sup_le_sup_right (h x) _))
  · refine EReal.neg_le_neg_iff.mpr ?_
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono fun x => EReal.toENNReal_le_toENNReal
        (sup_le_sup_right (EReal.neg_le_neg_iff.mpr (h x)) _))

lemma erealIntegral_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F] (μ : Measure E)
    {h : E → F} (hh : Measurable h) {v : F → EReal} (hv : Measurable v) :
    erealIntegral (μ.map h) v = erealIntegral μ (v ∘ h) := by
  unfold erealIntegral
  rw [lintegral_map (f := fun x => (v x ⊔ 0).toENNReal)
      ((hv.max measurable_const).ereal_toENNReal) hh,
    lintegral_map (f := fun x => ((-v x) ⊔ 0).toENNReal)
      ((hv.neg.max measurable_const).ereal_toENNReal) hh]
  rfl

lemma measurable_erealIntegral_kernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) [IsSFiniteKernel κ] {f : X → Y → EReal}
    (hf : Measurable fun p : X × Y => f p.1 p.2) :
    Measurable fun x => erealIntegral (κ x) (f x) := by
  unfold erealIntegral
  have h1 : Measurable fun x => ∫⁻ y, (f x y ⊔ 0).toENNReal ∂κ x :=
    (hf.max measurable_const).ereal_toENNReal.lintegral_kernel_prod_right'
  have h2 : Measurable fun x => ∫⁻ y, ((-f x y) ⊔ 0).toENNReal ∂κ x :=
    (hf.neg.max measurable_const).ereal_toENNReal.lintegral_kernel_prod_right'
  exact (measurable_coe_ennreal_ereal.comp h1).add (measurable_coe_ennreal_ereal.comp h2).neg

/-- The kernel `p ↦ ρ` reading off the probability-measure coordinate. -/
noncomputable def pmKernel {X : Type*} [MeasurableSpace X] (g : X → ProbabilityMeasure EY)
    (hg : Measurable g) : Kernel X EY where
  toFun x := (g x : Measure EY)
  measurable' := measurable_subtype_coe.comp hg

instance {X : Type*} [MeasurableSpace X] (g : X → ProbabilityMeasure EY) (hg : Measurable g) :
    IsMarkovKernel (pmKernel g hg) :=
  ⟨fun x => (g x).2⟩

variable (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M) (M' : FilteredModel M Fd)

lemma measurable_rprime :
    Measurable fun p : (EX × ProbabilityMeasure EY) × A => FilteredModel.rprime M p.1 p.2 := by
  have := measurable_erealIntegral_kernel (pmKernel (fun p : (EX × ProbabilityMeasure EY) × A =>
      p.1.2) (measurable_snd.comp measurable_fst))
    (f := fun p y => (M.r (p.1.1, y, p.2) : EReal))
    (measurable_coe_real_ereal.comp (M.hr_meas.comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))))
  exact this

lemma measurable_gprime :
    Measurable fun e : EX × ProbabilityMeasure EY => FilteredModel.gprime M e := by
  have := measurable_erealIntegral_kernel (pmKernel (fun e : EX × ProbabilityMeasure EY =>
      e.2) measurable_snd)
    (f := fun e y => (M.g (e.1, y) : EReal))
    (measurable_coe_real_ereal.comp (M.hg_meas.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  exact this

/-- The graph map `x' ↦ (x', Φ(x,ρ,a,x'))`. -/
lemma measurable_graph (x : EX) (ρ : ProbabilityMeasure EY) (a : A) :
    Measurable fun x' : EX => (x', Fd.Phi x ρ a x') := by
  have : Measurable fun x' : EX => Fd.Phi x ρ a x' :=
    Fd.hPhi_meas.comp ((measurable_const : Measurable fun _ : EX => (x, ρ)).prodMk
      ((measurable_const : Measurable fun _ : EX => a).prodMk measurable_id))
  exact measurable_id.prodMk this

lemma isProb_QXprime (x : EX) (ρ : ProbabilityMeasure EY) (a : A) :
    IsProbabilityMeasure (Fd.QXprime M x ρ a) := by
  have := M.isMarkovQ
  have hk : Measurable fun y : EY => (M.Q ((x, y), a)).map Prod.fst :=
    (Measure.measurable_map _ measurable_fst).comp
      (M.Q.measurable.comp ((measurable_const.prodMk measurable_id).prodMk measurable_const))
  constructor
  rw [FilterData.QXprime, Measure.bind_apply MeasurableSet.univ hk.aemeasurable]
  simp [Measure.map_apply measurable_fst MeasurableSet.univ]

instance isMarkov_Qprime : IsMarkovKernel M'.Qprime := by
  constructor
  rintro ⟨⟨x, ρ⟩, a⟩
  rw [M'.hQprime]
  have := isProb_QXprime M Fd x ρ a
  exact Measure.isProbabilityMeasure_map (measurable_graph M Fd x ρ a).aemeasurable

/-! ### The value-iteration functions -/

/-- `V 0 = g'`, `V (k+1) = T' (V k)`. -/
noncomputable def V : ℕ → EX × ProbabilityMeasure EY → EReal
  | 0 => FilteredModel.gprime M
  | k + 1 => fun e => FilteredModel.Tprime M Fd M' (V k) e

lemma V_zero : V M Fd M' 0 = FilteredModel.gprime M := rfl

lemma V_succ (k : ℕ) (e : EX × ProbabilityMeasure EY) :
    V M Fd M' (k + 1) e = FilteredModel.Tprime M Fd M' (V M Fd M' k) e := rfl

/-- Upper bound: any feasible history-dependent policy earns at most `V`. -/
lemma exprime_le_V (π : Policy EX A) (n : ℕ)
    (hfeas : ∀ j < n, ∀ xs as, π j xs as ∈ M.Dx (xs j)) :
    ∀ k j, j + k ≤ n → ∀ xs as ρ,
      FilteredModel.ExPrime M Fd M' π k j xs as ρ ≤ V M Fd M' k (xs j, ρ) := by
  intro k
  induction k with
  | zero => intro j _ xs as ρ; exact le_rfl
  | succ k ih =>
    intro j hj xs as ρ
    rw [V_succ]
    simp only [FilteredModel.ExPrime, FilteredModel.Tprime]
    refine le_trans ?_ (le_iSup₂_of_le (π j xs as) (hfeas j (by omega) xs as) le_rfl)
    refine add_le_add_right ?_ _
    refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast M.hβ0.le)
    refine erealIntegral_mono _ fun e' => ?_
    have := ih (j + 1) (by omega) (Function.update xs (j + 1) e'.1)
      (Function.update as j (π j xs as)) e'.2
    simpa using this

/-! ### The filter recursion started at an arbitrary prior -/

/-- `ρ_0 = ρ0`, `ρ_{j+1} = Φ(x_j, ρ_j, a_j, x_{j+1})`. -/
noncomputable def recon (ρ0 : ProbabilityMeasure EY) :
    ℕ → (ℕ → EX) → (ℕ → A) → ProbabilityMeasure EY
  | 0, _, _ => ρ0
  | j + 1, xs, as => Fd.Phi (xs j) (recon ρ0 j xs as) (as j) (xs (j + 1))

lemma mu_eq_recon (j : ℕ) (xs : ℕ → EX) (as : ℕ → A) :
    Fd.mu M j xs as = recon M Fd ⟨M.Q0, M.isProbQ0⟩ j xs as := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [FilterData.mu, recon, ih]

lemma recon_congr (ρ0 : ProbabilityMeasure EY) (j : ℕ) {xs xs' : ℕ → EX} {as as' : ℕ → A}
    (hx : ∀ i ≤ j, xs i = xs' i) (ha : ∀ i < j, as i = as' i) :
    recon M Fd ρ0 j xs as = recon M Fd ρ0 j xs' as' := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [recon]
    rw [ih (fun i hi => hx i (by omega)) (fun i hi => ha i (by omega)), hx j (by omega),
      ha j (by omega), hx (j + 1) le_rfl]

lemma measurable_recon (ρ0 : ProbabilityMeasure EY) (j : ℕ) :
    Measurable fun p : (ℕ → EX) × (ℕ → A) => recon M Fd ρ0 j p.1 p.2 := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    exact Fd.hPhi_meas.comp ((((measurable_pi_apply j).comp measurable_fst).prodMk ih).prodMk
      (((measurable_pi_apply j).comp measurable_snd).prodMk
        ((measurable_pi_apply (j + 1)).comp measurable_fst)))

/-! ### Measurability of the value of a measurable policy -/

lemma measurable_update_pair {P X : Type*} [MeasurableSpace P] [MeasurableSpace X] (i : ℕ)
    {f : P → ℕ → X} {g : P → X} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => Function.update (f p) i (g p) :=
  measurable_update'.comp (hf.prodMk hg)

lemma measurable_ExPrime [Nonempty A] (π : Policy EX A) (n : ℕ)
    (hπ : ∀ j < n, Measurable fun p : (ℕ → EX) × (ℕ → A) => π j p.1 p.2) :
    ∀ k j, j + k ≤ n → Measurable fun p : ((ℕ → EX) × (ℕ → A)) × ProbabilityMeasure EY =>
      FilteredModel.ExPrime M Fd M' π k j p.1.1 p.1.2 p.2 := by
  intro k
  induction k with
  | zero =>
    intro j _
    exact (measurable_gprime M).comp
      (((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  | succ k ih =>
    intro j hj
    simp only [FilteredModel.ExPrime]
    have hg : Measurable fun p : ((ℕ → EX) × (ℕ → A)) × ProbabilityMeasure EY =>
        ((p.1.1 j, p.2), π j p.1.1 p.1.2) :=
      (((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)).prodMk
        measurable_snd).prodMk ((hπ j (by omega)).comp measurable_fst)
    refine ((measurable_rprime M).comp hg).add (Measurable.const_mul ?_ _)
    have := measurable_erealIntegral_kernel (M'.Qprime.comap _ hg)
      (f := fun p e' => FilteredModel.ExPrime M Fd M' π k (j + 1)
        (Function.update p.1.1 (j + 1) e'.1) (Function.update p.1.2 j (π j p.1.1 p.1.2)) e'.2)
      ((ih (j + 1) (by omega)).comp ((((measurable_update_pair (j + 1)
          (measurable_fst.comp (measurable_fst.comp measurable_fst))
          (measurable_fst.comp measurable_snd))).prodMk
        (measurable_update_pair j (measurable_snd.comp (measurable_fst.comp measurable_fst))
          ((hπ j (by omega)).comp (measurable_fst.comp measurable_fst)))).prodMk
        (measurable_snd.comp measurable_snd)))
    exact this

/-! ### The policy built from maximizers attains `V` -/

lemma value_eq [Nonempty A] (ρ0 : ProbabilityMeasure EY) (n : ℕ)
    (f : ℕ → EX × ProbabilityMeasure EY → A)
    (hf : ∀ k, 1 ≤ k → k ≤ n → ∀ e, FilteredModel.rprime M e (f k e) +
      (M.β : EReal) * erealIntegral (M'.Qprime (e, f k e)) (V M Fd M' (k - 1)) = V M Fd M' k e)
    (hV : ∀ k ≤ n, Measurable (V M Fd M' k))
    (π : Policy EX A)
    (hπ : ∀ j < n, Measurable fun p : (ℕ → EX) × (ℕ → A) => π j p.1 p.2)
    (hπdef : ∀ j < n, ∀ xs as, π j xs as = f (n - j) (xs j, recon M Fd ρ0 j xs as)) :
    ∀ k j, j + k = n → ∀ xs as,
      FilteredModel.ExPrime M Fd M' π k j xs as (recon M Fd ρ0 j xs as) =
        V M Fd M' k (xs j, recon M Fd ρ0 j xs as) := by
  intro k
  induction k with
  | zero => intro j _ xs as; rfl
  | succ k ih =>
    intro j hj xs as
    set ρj := recon M Fd ρ0 j xs as with hρj
    set a := π j xs as with ha
    have haf : a = f (k + 1) (xs j, ρj) := by
      rw [ha, hπdef j (by omega)]; congr 1; omega
    have hW : Measurable fun e' : EX × ProbabilityMeasure EY =>
        FilteredModel.ExPrime M Fd M' π k (j + 1) (Function.update xs (j + 1) e'.1)
          (Function.update as j a) e'.2 :=
      (measurable_ExPrime M Fd M' π n hπ k (j + 1) (by omega)).comp
        (((measurable_update_pair (j + 1) measurable_const measurable_fst)).prodMk
          measurable_const |>.prodMk measurable_snd)
    have hint : erealIntegral (M'.Qprime ((xs j, ρj), a)) (fun e' =>
        FilteredModel.ExPrime M Fd M' π k (j + 1) (Function.update xs (j + 1) e'.1)
          (Function.update as j a) e'.2) =
        erealIntegral (M'.Qprime ((xs j, ρj), a)) (V M Fd M' k) := by
      rw [M'.hQprime, erealIntegral_map _ (measurable_graph M Fd _ _ _) hW,
        erealIntegral_map _ (measurable_graph M Fd _ _ _) (hV k (by omega))]
      congr 1
      funext x'
      simp only [Function.comp]
      have hrec : recon M Fd ρ0 (j + 1) (Function.update xs (j + 1) x')
          (Function.update as j a) = Fd.Phi (xs j) ρj a x' := by
        simp only [recon]
        have h1 : recon M Fd ρ0 j (Function.update xs (j + 1) x') (Function.update as j a) =
            ρj := recon_congr M Fd ρ0 j
              (fun i hi => by rw [Function.update_of_ne (by omega)])
              (fun i hi => by rw [Function.update_of_ne (by omega)])
        rw [h1, Function.update_of_ne (by omega), Function.update_self, Function.update_self]
      have := ih (j + 1) (by omega) (Function.update xs (j + 1) x') (Function.update as j a)
      rw [hrec, Function.update_self] at this
      exact this
    simp only [FilteredModel.ExPrime]
    rw [← ha, hint, V_succ]
    rw [haf]
    have := hf (k + 1) (by omega) (by omega) (xs j, ρj)
    simp only [Nat.add_sub_cancel] at this
    rw [this, V_succ]


/-! ### Assembling the argument -/

lemma exists_maximizers (N : ℕ) (hSAN : SAN M Fd M' N) :
    ∃ f : ℕ → EX × ProbabilityMeasure EY → A, ∀ k, Measurable (f k) ∧
      (∀ e, f k e ∈ M.Dx e.1) ∧
      (1 ≤ k → k ≤ N → ∀ e, FilteredModel.rprime M e (f k e) +
        (M.β : EReal) * erealIntegral (M'.Qprime (e, f k e)) (V M Fd M' (k - 1)) =
          V M Fd M' k e) := by
  obtain ⟨IM, Δ, hg, hT, hmax⟩ := hSAN
  have hIM : ∀ k ≤ N, V M Fd M' k ∈ IM (N - k) := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.sub_zero]; exact hg
    | succ k ih =>
      intro hk
      have := hT (N - k - 1) (by omega) (V M Fd M' k)
        (by rw [show N - k - 1 + 1 = N - k by omega]; exact ih (by omega))
      rw [show N - (k + 1) = N - k - 1 by omega]
      exact this
  obtain ⟨f0, hf0m, hf0D⟩ := M.hD_graph
  have : ∀ k, ∃ f : EX × ProbabilityMeasure EY → A, Measurable f ∧
      (∀ e, f e ∈ M.Dx e.1) ∧
      (1 ≤ k → k ≤ N → ∀ e, FilteredModel.rprime M e (f e) +
        (M.β : EReal) * erealIntegral (M'.Qprime (e, f e)) (V M Fd M' (k - 1)) =
          V M Fd M' k e) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k ≤ N
    · obtain ⟨f, -, hfm, hf⟩ := hmax (N - k) (by omega) (V M Fd M' (k - 1))
        (by rw [show N - k + 1 = N - (k - 1) by omega]; exact hIM (k - 1) (by omega))
      refine ⟨f, hfm, fun e => (hf e).1, fun _ _ e => ?_⟩
      rw [(hf e).2]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [V_succ, Nat.add_sub_cancel]
    · exact ⟨fun e => f0 e.1, hf0m.comp measurable_fst, fun e => hf0D e.1,
        fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose f hf using this
  exact ⟨f, hf⟩

lemma V_measurable (N : ℕ) (f : ℕ → EX × ProbabilityMeasure EY → A)
    (hfm : ∀ k, Measurable (f k))
    (hf : ∀ k, 1 ≤ k → k ≤ N → ∀ e, FilteredModel.rprime M e (f k e) +
      (M.β : EReal) * erealIntegral (M'.Qprime (e, f k e)) (V M Fd M' (k - 1)) = V M Fd M' k e) :
    ∀ k ≤ N, Measurable (V M Fd M' k) := by
  intro k
  induction k with
  | zero => intro _; exact measurable_gprime M
  | succ k ih =>
    intro hk
    have heq : V M Fd M' (k + 1) = fun e => FilteredModel.rprime M e (f (k + 1) e) +
        (M.β : EReal) * erealIntegral (M'.Qprime (e, f (k + 1) e)) (V M Fd M' k) := by
      funext e
      have := hf (k + 1) (by omega) hk e
      rw [Nat.add_sub_cancel] at this
      exact this.symm
    rw [heq]
    have hpair : Measurable fun e : EX × ProbabilityMeasure EY => (e, f (k + 1) e) :=
      measurable_id.prodMk (hfm (k + 1))
    refine ((measurable_rprime M).comp hpair).add (Measurable.const_mul ?_ _)
    exact (measurable_erealIntegral_kernel M'.Qprime (f := fun _ e' => V M Fd M' k e')
      ((ih (by omega)).comp measurable_snd)).comp hpair

lemma isPolicy_recon (n : ℕ) (ρ0 : ProbabilityMeasure EY) (g : ℕ → EX × ProbabilityMeasure EY → A)
    (hm : ∀ k, 1 ≤ k → k ≤ n → Measurable (g k))
    (hD : ∀ k, 1 ≤ k → k ≤ n → ∀ e, g k e ∈ M.Dx e.1) :
    M.IsPolicy n (fun j xs as => g (n - j) (xs j, recon M Fd ρ0 j xs as)) ∧
      ∀ j < n, Measurable fun p : (ℕ → EX) × (ℕ → A) =>
        g (n - j) (p.1 j, recon M Fd ρ0 j p.1 p.2) := by
  have hmeas : ∀ j < n, Measurable fun p : (ℕ → EX) × (ℕ → A) =>
      g (n - j) (p.1 j, recon M Fd ρ0 j p.1 p.2) := fun j hj =>
    (hm (n - j) (by omega) (by omega)).comp
      (((measurable_pi_apply j).comp measurable_fst).prodMk (measurable_recon M Fd ρ0 j))
  refine ⟨fun j hj => ⟨hmeas j hj, ?_, ?_⟩, hmeas⟩
  · intro xs xs' as as' hx ha
    simp only
    rw [hx j le_rfl, recon_congr M Fd ρ0 j hx ha]
  · intro xs as
    exact hD (n - j) (by omega) (by omega) (xs j, recon M Fd ρ0 j xs as)

lemma Jprime_eq_V [Nonempty A] (N : ℕ) (f : ℕ → EX × ProbabilityMeasure EY → A)
    (hfm : ∀ k, Measurable (f k)) (hfD : ∀ k e, f k e ∈ M.Dx e.1)
    (hf : ∀ k, 1 ≤ k → k ≤ N → ∀ e, FilteredModel.rprime M e (f k e) +
      (M.β : EReal) * erealIntegral (M'.Qprime (e, f k e)) (V M Fd M' (k - 1)) = V M Fd M' k e)
    (n : ℕ) (hn : n ≤ N) (x : EX) (ρ : ProbabilityMeasure EY) :
    FilteredModel.Jprime M Fd M' n x ρ = V M Fd M' n (x, ρ) := by
  apply le_antisymm
  · refine iSup₂_le fun π hπ => ?_
    exact exprime_le_V M Fd M' π n (fun j hj xs as => (hπ j hj).2.2 xs as) n 0 (by omega) _ _ ρ
  · obtain ⟨hpol, hmeas⟩ := isPolicy_recon M Fd n ρ f (fun k _ _ => hfm k) (fun k _ _ => hfD k)
    refine le_iSup₂_of_le _ hpol (le_of_eq ?_)
    have := value_eq M Fd M' ρ n f (fun k h1 h2 => hf k h1 (by omega))
      (fun k hk => V_measurable M Fd M' N f hfm hf k (by omega)) _ hmeas
      (fun j _ xs as => rfl) n 0 (by omega) (fun _ => x) (fun _ => Classical.arbitrary A)
    exact this.symm

end Sol533

end MDPFinance.POMDP

open MDPFinance.POMDP in
theorem solution {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY] [MeasurableSpace A]
    [Nonempty A] (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M)
    (M' : FilteredModel M Fd) (N : ℕ) (hInt : M.IntegrabilityAssumption N)
    (hSAN : ∃ (IM : ℕ → Set (EX × ProbabilityMeasure EY → EReal))
      (Δ : ℕ → Set (EX × ProbabilityMeasure EY → A)),
      FilteredModel.gprime M ∈ IM N ∧
        (∀ n < N, ∀ v ∈ IM (n + 1), (fun e => FilteredModel.Tprime M Fd M' v e) ∈ IM n) ∧
        ∀ n < N, ∀ v ∈ IM (n + 1), ∃ f ∈ Δ n, Measurable f ∧
          ∀ e : EX × ProbabilityMeasure EY, f e ∈ M.Dx e.1 ∧
            FilteredModel.rprime M e (f e) +
                (M.β : EReal) * erealIntegral (M'.Qprime (e, f e)) v =
              FilteredModel.Tprime M Fd M' v e) :
    (∀ x ρ, FilteredModel.Jprime M Fd M' 0 x ρ = FilteredModel.gprime M (x, ρ)) ∧
      (∀ n, 1 ≤ n → n ≤ N → ∀ (x : EX) (ρ : ProbabilityMeasure EY),
        FilteredModel.Jprime M Fd M' n x ρ =
          ⨆ a ∈ M.Dx x, FilteredModel.rprime M (x, ρ) a +
            (M.β : EReal) * erealIntegral (M'.Qprime ((x, ρ), a))
              (fun e' => FilteredModel.Jprime M Fd M' (n - 1) e'.1 e'.2)) ∧
      (∃ fprime : ℕ → EX × ProbabilityMeasure EY → A,
        ∀ n, 1 ≤ n → n ≤ N → Measurable (fprime n) ∧
          ∀ e : EX × ProbabilityMeasure EY, fprime n e ∈ M.Dx e.1 ∧
            FilteredModel.rprime M e (fprime n e) +
                (M.β : EReal) * erealIntegral (M'.Qprime (e, fprime n e))
                  (fun e' => FilteredModel.Jprime M Fd M' (n - 1) e'.1 e'.2) =
              FilteredModel.Jprime M Fd M' n e.1 e.2) ∧
      (∀ fprime : ℕ → EX × ProbabilityMeasure EY → A,
        (∀ n, 1 ≤ n → n ≤ N → Measurable (fprime n) ∧
          ∀ e : EX × ProbabilityMeasure EY, fprime n e ∈ M.Dx e.1 ∧
            FilteredModel.rprime M e (fprime n e) +
                (M.β : EReal) * erealIntegral (M'.Qprime (e, fprime n e))
                  (fun e' => FilteredModel.Jprime M Fd M' (n - 1) e'.1 e'.2) =
              FilteredModel.Jprime M Fd M' n e.1 e.2) →
        M.IsPolicy N (fun n xs as => fprime (N - n) (xs n, Fd.mu M n xs as)) ∧
          ∀ x0 : EX, M.JNpi (fun n xs as => fprime (N - n) (xs n, Fd.mu M n xs as)) N x0 =
            M.JN N x0) := by
  open Sol533 in
  obtain ⟨f, hf⟩ := exists_maximizers M Fd M' N hSAN
  have hfm : ∀ k, Measurable (f k) := fun k => (hf k).1
  have hfD : ∀ k e, f k e ∈ M.Dx e.1 := fun k => (hf k).2.1
  have hfV := fun k => (hf k).2.2
  have hJ : ∀ n ≤ N, ∀ x ρ, FilteredModel.Jprime M Fd M' n x ρ = V M Fd M' n (x, ρ) :=
    fun n hn x ρ => Jprime_eq_V M Fd M' N f hfm hfD hfV n hn x ρ
  have hJf : ∀ n ≤ N, (fun e' : EX × ProbabilityMeasure EY =>
      FilteredModel.Jprime M Fd M' n e'.1 e'.2) = V M Fd M' n :=
    fun n hn => funext fun e' => hJ n hn e'.1 e'.2
  have hV := V_measurable M Fd M' N f hfm hfV
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x ρ
    rw [hJ 0 (Nat.zero_le _)]
    rfl
  · intro n h1 h2 x ρ
    rw [hJ n h2, hJf (n - 1) (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, V_succ]
    rfl
  · refine ⟨f, fun n h1 h2 => ⟨hfm n, fun e => ⟨hfD n e, ?_⟩⟩⟩
    rw [hJf (n - 1) (by omega), hJ n h2]
    exact hfV n h1 h2 e
  · intro fp hfp
    have hfpV : ∀ k, 1 ≤ k → k ≤ N → ∀ e, FilteredModel.rprime M e (fp k e) +
        (M.β : EReal) * erealIntegral (M'.Qprime (e, fp k e)) (V M Fd M' (k - 1)) =
          V M Fd M' k e := by
      intro k h1 h2 e
      have := ((hfp k h1 h2).2 e).2
      rw [hJf (k - 1) (by omega), hJ k h2] at this
      exact this
    simp only [mu_eq_recon]
    obtain ⟨hpol, hmeas⟩ := isPolicy_recon M Fd N ⟨M.Q0, M.isProbQ0⟩ fp
      (fun k h1 h2 => (hfp k h1 h2).1) (fun k h1 h2 e => ((hfp k h1 h2).2 e).1)
    refine ⟨hpol, fun x0 => ?_⟩
    obtain ⟨h1, h2⟩ := theorem_5_3_2 M Fd M' N hInt _ hpol x0
    rw [h1, h2]
    refine Eq.trans ?_ (hJ N le_rfl x0 _).symm
    have := value_eq M Fd M' ⟨M.Q0, M.isProbQ0⟩ N fp hfpV hV _ hmeas
      (fun j _ xs as => rfl) N 0 (by omega) (fun _ => x0) (fun _ => Classical.arbitrary A)
    exact this
