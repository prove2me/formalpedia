-- Prove2me | solution 1 for MasulloGRH.sStdCharacter_pontryaginDual_equiv
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:01:58.219582+00:00
-- url     : https://prove2.me/submissions/196414ef-c743-4c05-84a1-51efb89c6278

import Mathlib
import Definitions.Def_MasulloGRH_SLocalStandardCharacter
import Theorems.Thm_MasulloGRH_stdAdelicCharacter_pontryaginDual_equiv

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_sStdCharacter_pontryaginDual_equiv

open MasulloGRH
open scoped Classical RestrictedProduct

noncomputable section

variable {F : Type*} [Field F] [NumberField F]
variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

section Part1

/-- The archimedean trace `Tr_∞ : F_∞ → ℝ`. -/
noncomputable def trInf (u : InfiniteAdeleRing F) : ℝ :=
  ∑ w : InfinitePlace F,
    (w.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding w (u w)).re

lemma trInf_add (u u' : InfiniteAdeleRing F) : trInf (u + u') = trInf u + trInf u' := by
  unfold trInf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (u + u') w = u w + u' w := rfl
  rw [h, map_add, Complex.add_re, mul_add]

lemma trInf_zero : trInf (0 : InfiniteAdeleRing F) = 0 := by
  unfold trInf
  refine Finset.sum_eq_zero fun w _ => ?_
  have h : (0 : InfiniteAdeleRing F) w = 0 := rfl
  rw [h, map_zero, Complex.zero_re, mul_zero]

lemma trInf_neg (u : InfiniteAdeleRing F) : trInf (-u) = -trInf u := by
  unfold trInf
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (-u) w = -(u w) := rfl
  rw [h, map_neg, Complex.neg_re, mul_neg]

lemma trInf_sub (u u' : InfiniteAdeleRing F) : trInf (u - u') = trInf u - trInf u' := by
  rw [sub_eq_add_neg, trInf_add, trInf_neg, sub_eq_add_neg]

/-- `∑_w mult(w) Re(σ_w(a)) = Tr_{F/ℚ}(a)`. -/
lemma sum_mult_re_embedding (a : F) :
    ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding a).re =
      ((Algebra.trace ℚ F a : ℚ) : ℝ) := by
  classical
  have h1 : ((Algebra.trace ℚ F a : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ a := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := a)
    rw [eq_ratCast] at h
    rw [h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ => φ a) (fun σ => σ a)
      (fun _ => rfl)).symm
  have h2 : ((Algebra.trace ℚ F a : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ a).re := by
    have h := congrArg Complex.re h1
    rw [Complex.re_sum] at h
    simpa using h
  rw [h2, ← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ : F →+* ℂ => (φ a).re)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h3 : ∀ φ ∈ (Finset.univ.filter fun φ : F →+* ℂ => InfinitePlace.mk φ = w),
      (φ a).re = (w.embedding a).re := by
    intro φ hφ
    have hφ' := (Finset.mem_filter.mp hφ).2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff] at hφ'
    rcases hφ' with h | h
    · rw [h]
    · rw [← h]; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [Finset.sum_congr rfl h3, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

lemma trInf_algebraMap (a : F) :
    trInf (algebraMap F (InfiniteAdeleRing F) a) = ((Algebra.trace ℚ F a : ℚ) : ℝ) := by
  rw [← sum_mult_re_embedding]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [InfiniteAdeleRing.algebraMap_apply]
  congr 2
  simp

lemma trace_int (a : 𝓞 F) : ∃ n : ℤ, ((Algebra.trace ℚ F (a : F) : ℚ) : ℝ) = n := by
  refine ⟨Algebra.intTrace ℤ (𝓞 F) a, ?_⟩
  have h := Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := F) (B := 𝓞 F) a
  rw [← h]
  simp

lemma sDiagonal_fst (ξ : F) : (sDiagonal Sf ξ).1 = algebraMap F (InfiniteAdeleRing F) ξ := rfl

lemma sDiagonal_snd (ξ : F) (v : Sf) :
    (sDiagonal Sf ξ).2 v =
      algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) ξ := rfl

lemma valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (ξ : F) :
    Valued.v (algebraMap F (v.adicCompletion F) ξ) = v.valuation F ξ :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ξ

/-- `ξ` is an `S`-integer approximating `x` modulo `∏_{v ∈ S_f} 𝒪_v`. -/
def IsApprox (x : SAdeleRing F Sf) (ξ : F) : Prop :=
  ξ ∈ SIntegers (F := F) Sf ∧
    ∀ v : Sf, (x - sDiagonal Sf ξ).2 v ∈
      (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F

/-- An element of `𝒪_{F,S}` that is integral at all places of `S_f` is in `𝒪_F`. -/
lemma mem_range_of_forall (δ : F) (h1 : δ ∈ SIntegers (F := F) Sf)
    (h2 : ∀ v ∈ Sf, v.valuation F δ ≤ 1) : δ ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F δ fun v => ?_
  by_cases hv : v ∈ Sf
  · exact h2 v hv
  · exact h1 v hv

/-- Well-definedness of the standard character. -/
lemma sStdCharacter_eq (x : SAdeleRing F Sf) (ξ : F) (h : IsApprox Sf x ξ) :
    sStdCharacter Sf x =
      Complex.exp (-(2 * Real.pi * Complex.I) * (trInf ((x - sDiagonal Sf ξ).1) : ℂ)) := by
  have hex : ∃ ξ : F, ξ ∈ SIntegers (F := F) Sf ∧
      ∀ v : Sf, (x - sDiagonal Sf ξ).2 v ∈
        (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F := ⟨ξ, h⟩
  unfold sStdCharacter
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set ξ' := hex.choose with hξ'
  have hsum : (∑ w : InfinitePlace F, (w.mult : ℂ) *
      ((InfinitePlace.Completion.extensionEmbedding w ((x - sDiagonal Sf ξ').1 w)).re : ℂ)) =
      ((trInf ((x - sDiagonal Sf ξ').1) : ℝ) : ℂ) := by
    simp [trInf]
  rw [hsum]
  -- δ = ξ' - ξ is in 𝓞 F
  have hδ : ξ' - ξ ∈ (algebraMap (𝓞 F) F).range := by
    refine mem_range_of_forall Sf _ (Subalgebra.sub_mem _ h1 h.1) fun v hv => ?_
    have e1 := h.2 ⟨v, hv⟩
    have e2 := h2 ⟨v, hv⟩
    have e3 : (x - sDiagonal Sf ξ).2 ⟨v, hv⟩ - (x - sDiagonal Sf ξ').2 ⟨v, hv⟩ ∈
        v.adicCompletionIntegers F := sub_mem e1 e2
    have e4 : (x - sDiagonal Sf ξ).2 ⟨v, hv⟩ - (x - sDiagonal Sf ξ').2 ⟨v, hv⟩ =
        algebraMap F (v.adicCompletion F) (ξ' - ξ) := by
      simp only [Prod.snd_sub, Pi.sub_apply, sDiagonal_snd, map_sub]
      ring
    rw [e4, HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap] at e3
    exact e3
  obtain ⟨a, ha⟩ := hδ
  obtain ⟨n, hn⟩ := trace_int a
  have e5 : (x - sDiagonal Sf ξ').1 = (x - sDiagonal Sf ξ).1 -
      algebraMap F (InfiniteAdeleRing F) (ξ' - ξ) := by
    simp only [Prod.fst_sub, sDiagonal_fst, map_sub]
    ring
  have ha' : (algebraMap (𝓞 F) F) a = ξ' - ξ := ha
  rw [e5, trInf_sub, trInf_algebraMap, ← ha', hn, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨n, ?_⟩
  push_cast
  ring

end Part1

/-- The projection `𝔸_F → 𝔸_{F,S}`. -/
def proj : AdeleRing (𝓞 F) F →+ SAdeleRing F Sf where
  toFun a := (a.1, fun v => a.2 (v : HeightOneSpectrum (𝓞 F)))
  map_zero' := rfl
  map_add' _ _ := rfl

lemma proj_mul (a b : AdeleRing (𝓞 F) F) : proj Sf (a * b) = proj Sf a * proj Sf b := rfl

lemma continuous_proj : Continuous (proj Sf) := by
  refine Continuous.prodMk continuous_fst ?_
  refine continuous_pi fun v => ?_
  exact (RestrictedProduct.continuous_eval (v : HeightOneSpectrum (𝓞 F))).comp continuous_snd

/-- The finite part of the extension by zero. -/
def inclP (x : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]_[
      Filter.principal ((Sf : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] :=
  ⟨fun v => if h : v ∈ Sf then x ⟨v, h⟩ else 0, by
    rw [Filter.eventually_principal]
    intro v hv
    have hv' : v ∉ Sf := hv
    dsimp only
    rw [dif_neg hv']
    exact zero_mem _⟩

lemma inclP_apply (x : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
    (v : HeightOneSpectrum (𝓞 F)) :
    inclP Sf x v = if h : v ∈ Sf then x ⟨v, h⟩ else 0 := rfl

omit [NumberField F] in
lemma cofinite_le : Filter.cofinite ≤ Filter.principal ((Sf : Set (HeightOneSpectrum (𝓞 F)))ᶜ) :=
  Filter.le_principal_iff.mpr (Sf.finite_toSet.compl_mem_cofinite)

/-- The underlying function of the extension by zero. -/
def inclFun (x : SAdeleRing F Sf) : AdeleRing (𝓞 F) F :=
  (x.1, RestrictedProduct.inclusion _ _ (cofinite_le Sf) (inclP Sf x.2))

lemma inclFun_snd_apply (x : SAdeleRing F Sf) (v : HeightOneSpectrum (𝓞 F)) :
    (inclFun Sf x).2 v = if h : v ∈ Sf then x.2 ⟨v, h⟩ else 0 := rfl

/-- Extension by zero `𝔸_{F,S} → 𝔸_F`. -/
def incl : SAdeleRing F Sf →+ AdeleRing (𝓞 F) F where
  toFun := inclFun Sf
  map_zero' := by
    refine Prod.ext rfl ?_
    refine FiniteAdeleRing.ext _ fun v => ?_
    rw [inclFun_snd_apply]
    split_ifs <;> rfl
  map_add' x y := by
    refine Prod.ext rfl ?_
    refine FiniteAdeleRing.ext _ fun v => ?_
    show (inclFun Sf (x + y)).2 v = (inclFun Sf x).2 v + (inclFun Sf y).2 v
    rw [inclFun_snd_apply, inclFun_snd_apply, inclFun_snd_apply]
    split_ifs
    · rfl
    · exact (add_zero _).symm

lemma continuous_inclP : Continuous (inclP Sf) := by
  refine RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun v => ?_
  by_cases h : v ∈ Sf
  · refine (continuous_apply (⟨v, h⟩ : Sf)).congr fun x => ?_
    simp only [Function.comp_apply, inclP_apply, dif_pos h]
  · refine (continuous_const (y := (0 : v.adicCompletion F))).congr fun x => ?_
    simp only [Function.comp_apply, inclP_apply, dif_neg h]

lemma continuous_incl : Continuous (incl Sf) := by
  have h2 : Continuous fun x : SAdeleRing F Sf =>
      RestrictedProduct.inclusion _ _ (cofinite_le Sf) (inclP Sf x.2) :=
    (RestrictedProduct.continuous_inclusion (cofinite_le Sf)).comp
      ((continuous_inclP Sf).comp continuous_snd)
  exact Continuous.prodMk continuous_fst h2

lemma incl_snd_apply (x : SAdeleRing F Sf) (v : HeightOneSpectrum (𝓞 F)) :
    (incl Sf x).2 v = if h : v ∈ Sf then x.2 ⟨v, h⟩ else 0 := rfl

lemma incl_fst (x : SAdeleRing F Sf) : (incl Sf x).1 = x.1 := rfl

lemma proj_incl (x : SAdeleRing F Sf) : proj Sf (incl Sf x) = x := by
  refine Prod.ext rfl (funext fun v => ?_)
  show (incl Sf x).2 (v : HeightOneSpectrum (𝓞 F)) = x.2 v
  rw [incl_snd_apply, dif_pos v.2]

lemma incl_mul (x : SAdeleRing F Sf) (z : AdeleRing (𝓞 F) F) :
    incl Sf x * z = incl Sf (x * proj Sf z) := by
  refine Prod.ext rfl ?_
  refine FiniteAdeleRing.ext _ fun v => ?_
  show (incl Sf x).2 v * z.2 v = (incl Sf (x * proj Sf z)).2 v
  rw [incl_snd_apply, incl_snd_apply]
  split_ifs with h
  · rfl
  · exact zero_mul _

/-- The standard character of `𝔸_F` restricted to `𝔸_{F,S}` (extended by zero) is `ψ_{S,std}`. -/
lemma stdAdelicCharacter_incl (x : SAdeleRing F Sf) :
    stdAdelicCharacter (incl Sf x) = sStdCharacter Sf x := by
  unfold stdAdelicCharacter
  split_ifs with h
  · obtain ⟨hy, ξ, hξ⟩ := h.choose_spec
    generalize h.choose = y at hy hξ ⊢
    have hcomp : ∀ v : HeightOneSpectrum (𝓞 F),
        (incl Sf x).2 v = y.2 v + algebraMap F (v.adicCompletion F) ξ := by
      intro v
      rw [hξ]
      rfl
    have happ : IsApprox Sf x ξ := by
      refine ⟨fun v hv => ?_, fun v => ?_⟩
      · have hv' : v ∉ Sf := hv
        have e1 := hcomp v
        rw [incl_snd_apply, dif_neg hv'] at e1
        have e2 : algebraMap F (v.adicCompletion F) ξ = -y.2 v := by
          rw [eq_neg_iff_add_eq_zero, add_comm, ← e1]
        have e3 : algebraMap F (v.adicCompletion F) ξ ∈ v.adicCompletionIntegers F := by
          rw [e2]
          exact neg_mem (hy v)
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap] at e3
        exact e3
      · have e1 := hcomp v
        rw [incl_snd_apply, dif_pos v.2] at e1
        have e2 : (x - sDiagonal Sf ξ).2 v = y.2 v := by
          simp only [Prod.snd_sub, Pi.sub_apply, sDiagonal_snd]
          rw [e1]
          ring
        rw [e2]
        exact hy v
    rw [sStdCharacter_eq Sf x ξ happ]
    have h1 : y.1 = (x - sDiagonal Sf ξ).1 := by
      have e1 : (incl Sf x).1 = y.1 + algebraMap F (InfiniteAdeleRing F) ξ := by
        rw [hξ]
        rfl
      rw [incl_fst] at e1
      rw [Prod.fst_sub, sDiagonal_fst, e1]
      ring
    rw [h1]
    simp [trInf]
  · unfold sStdCharacter
    rw [dif_neg]
    rintro ⟨ξ, hS, hv⟩
    apply h
    refine ⟨incl Sf x - algebraMap F (AdeleRing (𝓞 F) F) ξ, fun v => ?_, ξ, by ring⟩
    show (incl Sf x).2 v - algebraMap F (v.adicCompletion F) ξ ∈ v.adicCompletionIntegers F
    rw [incl_snd_apply]
    split_ifs with hvS
    · have e := hv ⟨v, hvS⟩
      simpa only [Prod.snd_sub, Pi.sub_apply, sDiagonal_snd] using e
    · rw [zero_sub]
      refine neg_mem ?_
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
      exact hS v hvS

end

end Sol_MasulloGRH_sStdCharacter_pontryaginDual_equiv

open MasulloGRH Sol_MasulloGRH_sStdCharacter_pontryaginDual_equiv in
theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ e : Multiplicative (SAdeleRing F Sf) ≃ₜ* PontryaginDual (Multiplicative (SAdeleRing F Sf)),
      ∀ x y : SAdeleRing F Sf,
        ((e (Multiplicative.ofAdd y) (Multiplicative.ofAdd x) : Circle) : ℂ) =
          sStdCharacter Sf (x * y) := by
  obtain ⟨eF, hF⟩ := MasulloGRH.stdAdelicCharacter_pontryaginDual_equiv F
  let ιh : Multiplicative (SAdeleRing F Sf) →ₜ* Multiplicative (AdeleRing (𝓞 F) F) :=
    { toMonoidHom := (incl Sf).toMultiplicative
      continuous_toFun := continuous_incl Sf }
  let ph : Multiplicative (AdeleRing (𝓞 F) F) →ₜ* Multiplicative (SAdeleRing F Sf) :=
    { toMonoidHom := (proj Sf).toMultiplicative
      continuous_toFun := continuous_proj Sf }
  -- the pairing of `𝔸_F` in terms of `eF`
  have hF' : ∀ (a z : Multiplicative (AdeleRing (𝓞 F) F)),
      ((eF a z : Circle) : ℂ) =
        stdAdelicCharacter (Multiplicative.toAdd z * Multiplicative.toAdd a) :=
    fun a z => hF z.toAdd a.toAdd
  have hι : ∀ b : Multiplicative (SAdeleRing F Sf),
      ιh b = Multiplicative.ofAdd (incl Sf (Multiplicative.toAdd b)) := fun _ => rfl
  have hp : ∀ a : Multiplicative (AdeleRing (𝓞 F) F),
      ph a = Multiplicative.ofAdd (proj Sf (Multiplicative.toAdd a)) := fun _ => rfl
  have hpι : ∀ b : Multiplicative (SAdeleRing F Sf), ph (ιh b) = b := fun b =>
    proj_incl Sf (Multiplicative.toAdd b)
  let toFun : Multiplicative (SAdeleRing F Sf) → PontryaginDual (Multiplicative (SAdeleRing F Sf)) :=
    fun b => PontryaginDual.map ιh (eF (ιh b))
  let invFun : PontryaginDual (Multiplicative (SAdeleRing F Sf)) → Multiplicative (SAdeleRing F Sf) :=
    fun χ => ph (eF.symm (PontryaginDual.map ph χ))
  have hleft : ∀ b, invFun (toFun b) = b := by
    intro b
    have key : PontryaginDual.map ph (toFun b) = eF (ιh b) := by
      refine PontryaginDual.ext fun z => Circle.ext ?_
      rw [PontryaginDual.map_apply]
      show ((eF (ιh b) (ιh (ph z)) : Circle) : ℂ) = ((eF (ιh b) z : Circle) : ℂ)
      rw [hF', hF']
      simp only [hι, hp, toAdd_ofAdd]
      congr 1
      rw [mul_comm, incl_mul, proj_incl, mul_comm (Multiplicative.toAdd z), incl_mul]
    show ph (eF.symm (PontryaginDual.map ph (toFun b))) = b
    rw [key, ContinuousMulEquiv.symm_apply_apply, hpι]
  have hright : ∀ χ, toFun (invFun χ) = χ := by
    intro χ
    set a := eF.symm (PontryaginDual.map ph χ) with ha
    have ha' : eF a = PontryaginDual.map ph χ := by
      rw [ha, ContinuousMulEquiv.apply_symm_apply]
    refine PontryaginDual.ext fun x => Circle.ext ?_
    show ((eF (ιh (ph a)) (ιh x) : Circle) : ℂ) = ((χ x : Circle) : ℂ)
    have hx : χ x = PontryaginDual.map ph χ (ιh x) := by
      rw [PontryaginDual.map_apply, hpι]
    rw [hx, ← ha', hF', hF']
    simp only [hι, hp, toAdd_ofAdd]
    congr 1
    rw [incl_mul, proj_incl, incl_mul]
  let e : Multiplicative (SAdeleRing F Sf) ≃ₜ* PontryaginDual (Multiplicative (SAdeleRing F Sf)) :=
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_mul' := fun b c => by
        show PontryaginDual.map ιh (eF (ιh (b * c))) =
          PontryaginDual.map ιh (eF (ιh b)) * PontryaginDual.map ιh (eF (ιh c))
        rw [map_mul, map_mul, map_mul]
      continuous_toFun :=
        (PontryaginDual.map ιh).continuous.comp (eF.continuous.comp ιh.continuous)
      continuous_invFun :=
        ph.continuous.comp (eF.symm.continuous.comp (PontryaginDual.map ph).continuous) }
  refine ⟨e, fun x y => ?_⟩
  show ((eF (ιh (Multiplicative.ofAdd y)) (ιh (Multiplicative.ofAdd x)) : Circle) : ℂ) =
    sStdCharacter Sf (x * y)
  rw [hF']
  simp only [hι, toAdd_ofAdd]
  rw [incl_mul, proj_incl, stdAdelicCharacter_incl]
