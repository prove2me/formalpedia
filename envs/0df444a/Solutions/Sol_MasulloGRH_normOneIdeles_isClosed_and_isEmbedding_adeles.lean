-- Prove2me | solution 1 for MasulloGRH.normOneIdeles_isClosed_and_isEmbedding_adeles
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T20:16:04.156205+00:00
-- url     : https://prove2.me/submissions/d8a8fa61-dd06-4829-bdff-edac1d9c9fed

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm

open NumberField IsDedekindDomain Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_normOneIdeles_isClosed_and_isEmbedding_adeles

open MasulloGRH Filter
open scoped RestrictedProduct

variable {F : Type*} [Field F] [NumberField F]

/-- The norm at a finite place: if `‖x‖ < 1` then `‖x‖ ≤ N(v)⁻¹`. -/
lemma norm_le_inv_absNorm_of_lt_one (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (hx : ‖x‖ < 1) : ‖x‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  have h1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  rw [FinitePlace.norm_def] at hx ⊢
  by_cases h0 : Valued.v x = 0
  · rw [WithZeroMulInt.toNNReal_pos_apply _ h0]
    simp only [NNReal.coe_zero]
    positivity
  · rw [WithZeroMulInt.toNNReal_neg_apply _ h0] at hx ⊢
    push_cast at hx ⊢
    have hk : (WithZero.unzero h0).toAdd < 0 := by
      by_contra hk
      push_neg at hk
      have := one_le_zpow₀ h1.le hk
      linarith
    have hk' : (WithZero.unzero h0).toAdd ≤ -1 := by omega
    calc ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.unzero h0).toAdd
        ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ h1.le hk'
      _ = _ := zpow_neg_one _

lemma two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) :
    (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have := HeightOneSpectrum.one_lt_absNorm v
  exact_mod_cast this

lemma norm_le_one_iff_mem (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F :=
  (Valued.toNormedField.norm_le_one_iff).trans (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm


local notation "𝔸" => AdeleRing (𝓞 F) F

/-- The finite component at `v` of an idele times that of its inverse is `1`. -/
lemma fin_mul_inv (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    (g : 𝔸).2 v * ((g⁻¹ : IdeleGroup F) : 𝔸).2 v = 1 := by
  have h : (g : 𝔸) * ((g⁻¹ : IdeleGroup F) : 𝔸) = 1 := g.mul_inv
  exact congrArg (fun a : 𝔸 => a.2 v) h

/-- The component at an infinite place `w` of an idele times that of its inverse is `1`. -/
lemma inf_mul_inv (g : IdeleGroup F) (w : InfinitePlace F) :
    (g : 𝔸).1 w * ((g⁻¹ : IdeleGroup F) : 𝔸).1 w = 1 := by
  have h : (g : 𝔸) * ((g⁻¹ : IdeleGroup F) : 𝔸) = 1 := g.mul_inv
  exact congrArg (fun a : 𝔸 => a.1 w) h

lemma norm_fin_eq_one_of_mem (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (g : 𝔸).2 v ∈ v.adicCompletionIntegers F)
    (h2 : ((g⁻¹ : IdeleGroup F) : 𝔸).2 v ∈ v.adicCompletionIntegers F) :
    ‖(g : 𝔸).2 v‖ = 1 := by
  have a1 : ‖(g : 𝔸).2 v‖ ≤ 1 := (norm_le_one_iff_mem v _).mpr h1
  have a2 : ‖((g⁻¹ : IdeleGroup F) : 𝔸).2 v‖ ≤ 1 := (norm_le_one_iff_mem v _).mpr h2
  have hm : ‖(g : 𝔸).2 v‖ * ‖((g⁻¹ : IdeleGroup F) : 𝔸).2 v‖ = 1 := by
    rw [← norm_mul, fin_mul_inv, norm_one]
  refine le_antisymm a1 ?_
  calc (1 : ℝ) = ‖(g : 𝔸).2 v‖ * ‖((g⁻¹ : IdeleGroup F) : 𝔸).2 v‖ := hm.symm
    _ ≤ ‖(g : 𝔸).2 v‖ * 1 := mul_le_mul_of_nonneg_left a2 (norm_nonneg _)
    _ = _ := mul_one _

/-- All but finitely many finite components of an idele have norm `1`. -/
lemma finite_mulSupport_fin (g : IdeleGroup F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖(g : 𝔸).2 v‖).Finite := by
  have h1 : ∀ᶠ v in Filter.cofinite,
      (g : 𝔸).2 v ∈ v.adicCompletionIntegers F := (g : 𝔸).2.2
  have h2 : ∀ᶠ v in Filter.cofinite,
      ((g⁻¹ : IdeleGroup F) : 𝔸).2 v ∈ v.adicCompletionIntegers F :=
    ((g⁻¹ : IdeleGroup F) : 𝔸).2.2
  have h3 := h1.and h2
  rw [Filter.eventually_cofinite] at h3
  refine h3.subset ?_
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  simp only [Set.mem_ofPred_eq]
  intro h
  exact hv (norm_fin_eq_one_of_mem g v h.1 h.2)

/-- The partial product of local norms over the infinite places and the finite places in `T`. -/
noncomputable def partialNorm (T : Finset (HeightOneSpectrum (𝓞 F))) (ξ : 𝔸) : ℝ :=
  (∏ w : InfinitePlace F, ‖ξ.1 w‖ ^ w.mult) * ∏ v ∈ T, ‖ξ.2 v‖

lemma partialNorm_nonneg (T : Finset (HeightOneSpectrum (𝓞 F))) (ξ : 𝔸) :
    0 ≤ partialNorm T ξ := by
  unfold partialNorm
  exact mul_nonneg (Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _)
    (Finset.prod_nonneg fun v _ => norm_nonneg _)

lemma continuous_fin_coord (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (fun ξ : 𝔸 => ξ.2 v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

lemma continuous_inf_coord (w : InfinitePlace F) :
    Continuous (fun ξ : 𝔸 => ξ.1 w) :=
  (continuous_apply w).comp continuous_fst

lemma continuous_partialNorm (T : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (partialNorm (F := F) T) := by
  unfold partialNorm
  exact (continuous_finsetProd _ fun w _ => ((continuous_inf_coord w).norm.pow _)).mul
    (continuous_finsetProd _ fun v _ => (continuous_fin_coord v).norm)

/-- The adeles integral outside `T`. -/
def integralOutside (T : Finset (HeightOneSpectrum (𝓞 F))) : Set 𝔸 :=
  {ξ | ∀ v, v ∉ T → ξ.2 v ∈ v.adicCompletionIntegers F}

lemma isOpen_integralOutside (T : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (integralOutside (F := F) T) := by
  have : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ T → a.1 v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
  exact this.preimage continuous_snd

/-- Key estimate: a norm-one idele integral outside `T` whose partial norm over `T` is `< c`,
where `c ≤ N(v)` for all `v ∉ T`, has all components of norm one outside `T`. -/
lemma key (g : IdeleGroup F) (hg : ideleNorm g = 1) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : (g : 𝔸) ∈ integralOutside T) (c : ℝ)
    (hc : ∀ v, v ∉ T → c ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ))
    (hlt : partialNorm T (g : 𝔸) < c) :
    (∀ v, v ∉ T → ‖(g : 𝔸).2 v‖ = 1) ∧ partialNorm T (g : 𝔸) = 1 := by
  classical
  set M : Finset (HeightOneSpectrum (𝓞 F)) := T ∪ (finite_mulSupport_fin g).toFinset with hM
  have hTM : T ⊆ M := Finset.subset_union_left
  set q : ℝ := ∏ v ∈ M \ T, ‖(g : 𝔸).2 v‖ with hq
  have hsplit : ideleNorm g = partialNorm T (g : 𝔸) * q := by
    unfold ideleNorm partialNorm
    rw [finprod_eq_prod_of_mulSupport_subset (s := M) _ (by
      intro v hv; rw [hM, Finset.coe_union]; exact Or.inr (by simpa using hv))]
    rw [← Finset.prod_sdiff hTM]
    ring
  have hle1 : ∀ v, v ∉ T → ‖(g : 𝔸).2 v‖ ≤ 1 := fun v hv => (norm_le_one_iff_mem v _).mpr (hT v hv)
  have hP0 := partialNorm_nonneg T (g : 𝔸)
  have hc0 : 0 < c := lt_of_le_of_lt hP0 hlt
  have hall : ∀ v, v ∉ T → ‖(g : 𝔸).2 v‖ = 1 := by
    intro v hvT
    by_contra hne
    have hvM : v ∈ M \ T := by
      rw [Finset.mem_sdiff]
      refine ⟨?_, hvT⟩
      rw [hM, Finset.mem_union]
      exact Or.inr (by simpa using hne)
    have hlt1 : ‖(g : 𝔸).2 v‖ < 1 := lt_of_le_of_ne (hle1 v hvT) hne
    have hsmall : ‖(g : 𝔸).2 v‖ ≤ c⁻¹ :=
      (norm_le_inv_absNorm_of_lt_one v _ hlt1).trans (inv_anti₀ hc0 (hc v hvT))
    have hqle : q ≤ ‖(g : 𝔸).2 v‖ := by
      rw [hq, ← Finset.mul_prod_erase _ _ hvM]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      refine Finset.prod_le_one (fun u _ => norm_nonneg _) (fun u hu => ?_)
      exact hle1 u (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hu)).2
    have : (1 : ℝ) < 1 := by
      calc (1 : ℝ) = partialNorm T (g : 𝔸) * q := hg ▸ hsplit
        _ ≤ partialNorm T (g : 𝔸) * c⁻¹ := mul_le_mul_of_nonneg_left (hqle.trans hsmall) hP0
        _ < c * c⁻¹ := mul_lt_mul_of_pos_right hlt (inv_pos.mpr hc0)
        _ = 1 := mul_inv_cancel₀ hc0.ne'
    exact lt_irrefl _ this
  refine ⟨hall, ?_⟩
  have hq1 : q = 1 := by
    rw [hq]
    exact Finset.prod_eq_one fun v hv => hall v (Finset.mem_sdiff.mp hv).2
  rw [hsplit, hq1, mul_one] at hg
  exact hg


lemma norm_eq_one_iff (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ‖x‖ = 1 ↔ Valued.v x = 1 := by
  constructor
  · intro h
    refine le_antisymm (Valued.toNormedField.norm_le_one_iff.mp h.le) ?_
    exact not_lt.mp fun hlt => (Valued.toNormedField.norm_lt_one_iff.mpr hlt).ne h
  · intro h
    refine le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr h.le) ?_
    exact not_lt.mp fun hlt => (Valued.toNormedField.norm_lt_one_iff.mp hlt).ne h

lemma ideleNorm_eq_partialNorm (g : IdeleGroup F) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (h : ∀ v, v ∉ T → ‖(g : 𝔸).2 v‖ = 1) : ideleNorm g = partialNorm T (g : 𝔸) := by
  unfold ideleNorm partialNorm
  rw [finprod_eq_prod_of_mulSupport_subset (s := T) _ (by
    intro v hv
    by_contra hvT
    exact hv (h v hvT))]

lemma partialNorm_le_of_subset (T₀ T : Finset (HeightOneSpectrum (𝓞 F))) (hsub : T₀ ⊆ T)
    (x : 𝔸) (hx : x ∈ integralOutside T₀) : partialNorm T x ≤ partialNorm T₀ x := by
  classical
  unfold partialNorm
  rw [← Finset.prod_sdiff hsub]
  have h1 : ∏ v ∈ T \ T₀, ‖x.2 v‖ ≤ 1 :=
    Finset.prod_le_one (fun v _ => norm_nonneg _)
      (fun v hv => (norm_le_one_iff_mem v _).mpr (hx v (Finset.mem_sdiff.mp hv).2))
  have h0 : 0 ≤ ∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult :=
    Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _
  have h2 : 0 ≤ ∏ v ∈ T₀, ‖x.2 v‖ := Finset.prod_nonneg fun v _ => norm_nonneg _
  calc (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * ((∏ v ∈ T \ T₀, ‖x.2 v‖) * ∏ v ∈ T₀, ‖x.2 v‖)
      ≤ (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * (1 * ∏ v ∈ T₀, ‖x.2 v‖) := by
        gcongr
    _ = _ := by ring

lemma partialNorm_insert [DecidableEq (HeightOneSpectrum (𝓞 F))] (T : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ T) (x : 𝔸) : partialNorm (insert v T) x = partialNorm T x * ‖x.2 v‖ := by
  unfold partialNorm
  rw [Finset.prod_insert hv]
  ring

lemma isUnit_of_coords (x : 𝔸) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hinf : ∀ w, x.1 w ≠ 0) (hfin : ∀ v, x.2 v ≠ 0) (hone : ∀ v, v ∉ T → ‖x.2 v‖ = 1) :
    IsUnit x := by
  refine Prod.isUnit_iff.mpr ⟨Pi.isUnit_iff.mpr fun w => isUnit_iff_ne_zero.mpr (hinf w), ?_⟩
  refine FiniteAdeleRing.isUnit_iff.mpr ⟨hfin, ?_⟩
  filter_upwards [T.finite_toSet.eventually_cofinite_notMem] with v hv
  exact (norm_eq_one_iff v _).mp (hone v hv)

/-- The norm-one ideles, as a subset of the adeles. -/
def normOneSet : Set 𝔸 := (fun g : IdeleGroup F => (g : 𝔸)) '' {g | ideleNorm g = 1}

/-- Limits of norm-one ideles satisfy the dichotomy of the key estimate. -/
lemma closure_dichotomy (x : 𝔸) (hx : x ∈ closure (normOneSet (F := F)))
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hxT : x ∈ integralOutside T) (c : ℝ)
    (hc : ∀ v, v ∉ T → c ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)) :
    partialNorm T x = 1 ∨ c ≤ partialNorm T x := by
  by_contra hne
  push_neg at hne
  obtain ⟨hne1, hltc⟩ := hne
  set W : Set 𝔸 := integralOutside T ∩
    (partialNorm T) ⁻¹' ({r : ℝ | r = 1 ∨ c ≤ r}ᶜ) with hW
  have hZ : IsClosed {r : ℝ | r = 1 ∨ c ≤ r} := isClosed_eq continuous_id continuous_const |>.union
    (isClosed_le continuous_const continuous_id)
  have hWo : IsOpen W := (isOpen_integralOutside T).inter
    (hZ.isOpen_compl.preimage (continuous_partialNorm T))
  have hxW : x ∈ W := ⟨hxT, fun h => h.elim hne1 (fun h' => not_le.mpr hltc h')⟩
  obtain ⟨y, ⟨hyT, hyZ⟩, ⟨g, hg, rfl⟩⟩ := mem_closure_iff.mp hx W hWo hxW
  have hlt : partialNorm T (g : 𝔸) < c := by
    by_contra h
    exact hyZ (Or.inr (not_lt.mp h))
  exact hyZ (Or.inl (key g hg T hyT c hc hlt).2)

lemma isClosed_normOneSet : IsClosed (normOneSet (F := F)) := by
  classical
  refine isClosed_of_closure_subset fun x hx => ?_
  -- the finite set of places where `x` is not integral
  have hfin0 : {v : HeightOneSpectrum (𝓞 F) | ¬ x.2 v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp x.2.2
  set T₀ : Finset (HeightOneSpectrum (𝓞 F)) := hfin0.toFinset with hT₀
  have hxT₀ : x ∈ integralOutside T₀ := by
    intro v hv
    by_contra h
    exact hv (by simpa [hT₀] using h)
  set C : ℝ := partialNorm T₀ x with hC
  set n : ℕ := ⌊C⌋₊ + 1 with hn
  have hB : {v : HeightOneSpectrum (𝓞 F) | Ideal.absNorm v.asIdeal ≤ n}.Finite :=
    Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le n
  set T : Finset (HeightOneSpectrum (𝓞 F)) := T₀ ∪ hB.toFinset with hT
  set c : ℝ := (n : ℝ) + 1 with hc
  have hcN : ∀ v, v ∉ T → c ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    intro v hv
    have hvB : ¬ Ideal.absNorm v.asIdeal ≤ n := by
      intro h
      exact hv (Finset.mem_union.mpr (Or.inr (by simpa using h)))
    have : n + 1 ≤ Ideal.absNorm v.asIdeal := by omega
    rw [hc]
    exact_mod_cast this
  have hCc : C < c := by
    have h1 : C < (⌊C⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one C
    rw [hc, hn]
    push_cast
    linarith
  have hc1 : (1 : ℝ) < c := by
    rw [hc]
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have hT₀T : T₀ ⊆ T := Finset.subset_union_left
  have hxT : x ∈ integralOutside T := fun v hv => hxT₀ v (fun h => hv (hT₀T h))
  have hPT : partialNorm T x = 1 := by
    rcases closure_dichotomy x hx T hxT c hcN with h | h
    · exact h
    · exact absurd ((partialNorm_le_of_subset T₀ T hT₀T x hxT₀).trans_lt hCc) (not_lt.mpr h)
  -- every component outside `T` has norm one
  have hone : ∀ v, v ∉ T → ‖x.2 v‖ = 1 := by
    intro v hv
    have hle : ‖x.2 v‖ ≤ 1 := (norm_le_one_iff_mem v _).mpr (hxT v hv)
    have hxT' : x ∈ integralOutside (insert v T) := fun u hu => hxT u (fun h => hu (Finset.mem_insert_of_mem h))
    have hcN' : ∀ u, u ∉ insert v T → c ≤ ((Ideal.absNorm u.asIdeal : ℕ) : ℝ) :=
      fun u hu => hcN u (fun h => hu (Finset.mem_insert_of_mem h))
    rcases closure_dichotomy x hx (insert v T) hxT' c hcN' with h | h
    · rwa [partialNorm_insert T v hv, hPT, one_mul] at h
    · rw [partialNorm_insert T v hv, hPT, one_mul] at h
      linarith
  -- all components are nonzero
  have hprod : (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * ∏ v ∈ T, ‖x.2 v‖ = 1 := hPT
  have hinf : ∀ w, x.1 w ≠ 0 := by
    intro w hw
    have : (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hw, norm_zero, zero_pow (InfinitePlace.mult_ne_zero)])
    rw [this, zero_mul] at hprod
    exact zero_ne_one hprod
  have hfinne : ∀ v, x.2 v ≠ 0 := by
    intro v hv
    by_cases hvT : v ∈ T
    · have : ∏ v ∈ T, ‖x.2 v‖ = 0 := Finset.prod_eq_zero hvT (by rw [hv, norm_zero])
      rw [this, mul_zero] at hprod
      exact zero_ne_one hprod
    · have := hone v hvT
      rw [hv, norm_zero] at this
      exact zero_ne_one this
  have hu : IsUnit x := isUnit_of_coords x T hinf hfinne hone
  refine ⟨hu.unit, ?_, hu.unit_spec⟩
  show ideleNorm hu.unit = 1
  rw [ideleNorm_eq_partialNorm hu.unit T (by rw [hu.unit_spec]; exact hone), hu.unit_spec, hPT]


/-- Convergence in the finite adeles, for maps that are eventually integral outside a fixed
finite set `T`: it suffices to check convergence coordinatewise. -/
lemma tendsto_finiteAdele {X : Type*} {l : Filter X} {h : X → FiniteAdeleRing (𝓞 F) F}
    {b : FiniteAdeleRing (𝓞 F) F} (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hb : ∀ v, v ∉ T → b v ∈ v.adicCompletionIntegers F)
    (hev : ∀ᶠ x in l, ∀ v, v ∉ T → h x v ∈ v.adicCompletionIntegers F)
    (hcoord : ∀ v, Tendsto (fun x => h x v) l (𝓝 (b v))) : Tendsto h l (𝓝 b) := by
  classical
  set S : Set (HeightOneSpectrum (𝓞 F)) := (↑T)ᶜ with hSdef
  have hS : (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 S := by
    rw [le_principal_iff]
    exact T.finite_toSet.compl_mem_cofinite
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => Valued.isOpen_valuationSubring _
  let b' : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 S] :=
    ⟨b, eventually_principal.mpr (fun v hv => hb v hv)⟩
  have hbb : RestrictedProduct.inclusion _ _ hS b' = b := rfl
  let h' : X → Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 S] :=
    fun x => if H : ∀ v ∈ S, h x v ∈ v.adicCompletionIntegers F then
      RestrictedProduct.mk (fun v => h x v) (eventually_principal.mpr H) else b'
  have hh' : ∀ x, (∀ v, v ∉ T → h x v ∈ v.adicCompletionIntegers F) →
      RestrictedProduct.inclusion _ _ hS (h' x) = h x := by
    intro x hx
    have H : ∀ v ∈ S, h x v ∈ v.adicCompletionIntegers F := fun v hv => hx v hv
    have e : h' x = RestrictedProduct.mk (fun v => h x v) (eventually_principal.mpr H) := dif_pos H
    rw [e]
    rfl
  have heq : (fun x => RestrictedProduct.inclusion _ _ hS (h' x)) =ᶠ[l] h := by
    filter_upwards [hev] with x hx
    exact hh' x hx
  refine Tendsto.congr' heq ?_
  have key : 𝓝 b = map (RestrictedProduct.inclusion _ _ hS) (𝓝 b') :=
    RestrictedProduct.nhds_eq_map_inclusion hAopen hS b'
  rw [key]
  refine tendsto_map.comp ?_
  rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
  intro v
  refine (hcoord v).congr' ?_
  filter_upwards [hev] with x hx
  have := congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) (hh' x hx)
  exact this.symm


lemma inv_coord_fin (u : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    ((u⁻¹ : IdeleGroup F) : 𝔸).2 v = ((u : 𝔸).2 v)⁻¹ :=
  eq_inv_of_mul_eq_one_right (fin_mul_inv u v)

lemma inv_coord_inf (u : IdeleGroup F) (w : InfinitePlace F) :
    ((u⁻¹ : IdeleGroup F) : 𝔸).1 w = ((u : 𝔸).1 w)⁻¹ :=
  eq_inv_of_mul_eq_one_right (inf_mul_inv u w)

lemma fin_ne_zero (u : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) : (u : 𝔸).2 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (fin_mul_inv u v)

lemma inf_ne_zero (u : IdeleGroup F) (w : InfinitePlace F) : (u : 𝔸).1 w ≠ 0 :=
  left_ne_zero_of_mul_eq_one (inf_mul_inv u w)

/-- Inversion is continuous on the norm-one ideles for the adelic topology. -/
lemma continuousOn_inverse : ContinuousOn (Ring.inverse : 𝔸 → 𝔸) (normOneSet (F := F)) := by
  rintro _ ⟨g0, hg0, rfl⟩
  classical
  have hfinT : {v : HeightOneSpectrum (𝓞 F) | ¬ ((g0 : 𝔸).2 v ∈ v.adicCompletionIntegers F ∧
      ((g0⁻¹ : IdeleGroup F) : 𝔸).2 v ∈ v.adicCompletionIntegers F)}.Finite :=
    Filter.eventually_cofinite.mp ((g0 : 𝔸).2.2.and ((g0⁻¹ : IdeleGroup F) : 𝔸).2.2)
  set T : Finset (HeightOneSpectrum (𝓞 F)) := hfinT.toFinset with hTdef
  have hT1 : ∀ v, v ∉ T → ((g0 : 𝔸).2 v ∈ v.adicCompletionIntegers F ∧
      ((g0⁻¹ : IdeleGroup F) : 𝔸).2 v ∈ v.adicCompletionIntegers F) := by
    intro v hv
    by_contra h
    exact hv (by simpa [hTdef] using h)
  have hone0 : ∀ v, v ∉ T → ‖(g0 : 𝔸).2 v‖ = 1 :=
    fun v hv => norm_fin_eq_one_of_mem g0 v (hT1 v hv).1 (hT1 v hv).2
  have hP0 : partialNorm T (g0 : 𝔸) = 1 := (ideleNorm_eq_partialNorm g0 T hone0).symm.trans hg0
  set U : Set 𝔸 := integralOutside T ∩ {ξ | partialNorm T ξ < 2} with hUdef
  have hU : U ∈ 𝓝 (g0 : 𝔸) :=
    ((isOpen_integralOutside T).inter (isOpen_lt (continuous_partialNorm T) continuous_const)).mem_nhds
      ⟨fun v hv => (hT1 v hv).1, by rw [Set.mem_ofPred_eq, hP0]; norm_num⟩
  have hUY : normOneSet ∩ U ∈ 𝓝[normOneSet] (g0 : 𝔸) := inter_mem_nhdsWithin _ hU
  have hY : normOneSet ∈ 𝓝[normOneSet] (g0 : 𝔸) := self_mem_nhdsWithin
  have hinvY : ∀ ξ ∈ (normOneSet (F := F)), ∃ g : IdeleGroup F, ideleNorm g = 1 ∧ (g : 𝔸) = ξ ∧
      Ring.inverse ξ = ((g⁻¹ : IdeleGroup F) : 𝔸) := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl, Ring.inverse_unit g⟩
  rw [ContinuousWithinAt, Ring.inverse_unit g0]
  have h1 : Tendsto (fun ξ : 𝔸 => (Ring.inverse ξ).1) (𝓝[normOneSet] (g0 : 𝔸))
      (𝓝 ((g0⁻¹ : IdeleGroup F) : 𝔸).1) := by
    refine tendsto_pi_nhds.mpr fun w => ?_
    have hc : Tendsto (fun ξ : 𝔸 => (ξ.1 w)⁻¹) (𝓝[normOneSet] (g0 : 𝔸))
        (𝓝 (((g0⁻¹ : IdeleGroup F) : 𝔸).1 w)) := by
      rw [inv_coord_inf]
      exact ((continuous_inf_coord w).continuousAt.inv₀ (inf_ne_zero g0 w)).tendsto.mono_left
        nhdsWithin_le_nhds
    refine hc.congr' ?_
    filter_upwards [hY] with ξ hξ
    obtain ⟨g, hg, rfl, he⟩ := hinvY ξ hξ
    rw [he, inv_coord_inf]
  have h2 : Tendsto (fun ξ : 𝔸 => (Ring.inverse ξ).2) (𝓝[normOneSet] (g0 : 𝔸))
      (𝓝 ((g0⁻¹ : IdeleGroup F) : 𝔸).2) := by
    refine tendsto_finiteAdele T (fun v hv => (hT1 v hv).2) ?_ ?_
    · filter_upwards [hUY] with ξ hξ
      obtain ⟨hξY, hξU⟩ := hξ
      obtain ⟨g, hg, rfl, he⟩ := hinvY ξ hξY
      have hk := (key g hg T hξU.1 2 (fun v _ => two_le_absNorm v) hξU.2).1
      intro v hv
      rw [he, inv_coord_fin, ← norm_le_one_iff_mem, norm_inv, hk v hv, inv_one]
    · intro v
      have hc : Tendsto (fun ξ : 𝔸 => (ξ.2 v)⁻¹) (𝓝[normOneSet] (g0 : 𝔸))
          (𝓝 (((g0⁻¹ : IdeleGroup F) : 𝔸).2 v)) := by
        rw [inv_coord_fin]
        exact ((continuous_fin_coord v).continuousAt.inv₀ (fin_ne_zero g0 v)).tendsto.mono_left
          nhdsWithin_le_nhds
      refine hc.congr' ?_
      filter_upwards [hY] with ξ hξ
      obtain ⟨g, hg, rfl, he⟩ := hinvY ξ hξ
      rw [he, inv_coord_fin]
  exact h1.prodMk_nhds h2

lemma isEmbedding_normOne :
    IsEmbedding (fun g : {g : IdeleGroup F // ideleNorm g = 1} => ((g : IdeleGroup F) : 𝔸)) := by
  let f' : {g : IdeleGroup F // ideleNorm g = 1} → normOneSet (F := F) :=
    fun g => ⟨((g : IdeleGroup F) : 𝔸), ⟨g, g.2, rfl⟩⟩
  have hf' : Continuous f' := (Units.continuous_val.comp continuous_subtype_val).subtype_mk _
  let k' : normOneSet (F := F) → 𝔸 × 𝔸ᵐᵒᵖ :=
    fun y => ((y : 𝔸), MulOpposite.op (Ring.inverse (y : 𝔸)))
  have hk' : Continuous k' := continuous_subtype_val.prodMk
    (MulOpposite.continuous_op.comp (continuousOn_iff_continuous_domRestrict.mp continuousOn_inverse))
  have hcomp : k' ∘ f' = Units.embedProduct 𝔸 ∘ Subtype.val := by
    funext g
    refine Prod.ext rfl ?_
    show MulOpposite.op (Ring.inverse ((g : IdeleGroup F) : 𝔸)) =
      MulOpposite.op (((g : IdeleGroup F)⁻¹ : IdeleGroup F) : 𝔸)
    rw [Ring.inverse_unit]
  have hind : IsInducing (k' ∘ f') := by
    rw [hcomp]
    exact Units.isInducing_embedProduct.comp IsInducing.subtypeVal
  have hf'ind : IsInducing f' := IsInducing.of_comp hf' hk' hind
  refine ⟨IsInducing.subtypeVal.comp hf'ind, ?_⟩
  intro a b hab
  exact Subtype.ext (Units.ext hab)

end Sol_MasulloGRH_normOneIdeles_isClosed_and_isEmbedding_adeles

open MasulloGRH Sol_MasulloGRH_normOneIdeles_isClosed_and_isEmbedding_adeles in
theorem solution (F : Type*) [Field F] [NumberField F] :
    IsClosed ((fun g : IdeleGroup F => (g : AdeleRing (𝓞 F) F)) '' {g | ideleNorm g = 1}) ∧
      IsEmbedding (fun g : {g : IdeleGroup F // ideleNorm g = 1} =>
        ((g : IdeleGroup F) : AdeleRing (𝓞 F) F)) :=
  ⟨isClosed_normOneSet (F := F), isEmbedding_normOne (F := F)⟩
