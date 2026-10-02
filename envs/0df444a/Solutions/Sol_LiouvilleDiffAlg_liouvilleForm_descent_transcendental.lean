-- Prove2me | solution 1 for LiouvilleDiffAlg.liouvilleForm_descent_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T11:56:12.210013+00:00
-- url     : https://prove2.me/submissions/f70edd6d-da7b-4da6-8323-c6576965c5ea

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic
import Definitions.Def_LiouvilleDiffAlg_Form
import Theorems.Thm_LiouvilleDiffAlg_ratFunc_descent_log
import Theorems.Thm_LiouvilleDiffAlg_ratFunc_descent_exp

open scoped Differential
open Polynomial
open LiouvilleDiffAlg

set_option warn.classDefReducibility false
set_option linter.style.haveILetI false

private noncomputable def subDiff {F G : Type*} [Field F] [Field G] [Differential G] [Algebra F G]
    (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K) : Differential K :=
  ⟨Derivation.mk'
    { toFun := fun x => ⟨(x : G)′, hK x x.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun n x => Subtype.ext (by simp) }
    (fun a b => Subtype.ext (by simp [Derivation.leibniz]))⟩

private lemma subDiff_coe {F G : Type*} [Field F] [Field G] [Differential G] [Algebra F G]
    (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K) (x : K) :
    (((subDiff K hK).deriv x : K) : G) = (x : G)′ := rfl

private lemma subDiff_alg {F G : Type*} [Field F] [Field G] [Differential G] [Algebra F G]
    (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K) :
    @DifferentialAlgebra K G _ _ _ (subDiff K hK) _ :=
  @DifferentialAlgebra.mk K G _ _ _ (subDiff K hK) _ (fun _ => rfl)

private lemma closed_adjoin {F G : Type*} [Field F] [Field G] [Differential G] [Algebra F G]
    (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K) (t : G)
    (ht : t′ ∈ IntermediateField.adjoin K {t}) :
    ∀ x ∈ IntermediateField.adjoin K {t}, x′ ∈ IntermediateField.adjoin K {t} := by
  intro x hx
  refine IntermediateField.adjoin_induction (p := fun x _ => x′ ∈ IntermediateField.adjoin K {t})
    (mem := ?_) (algebraMap := ?_) (add := ?_) (inv := ?_) (mul := ?_) (h := hx)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ht
  · intro x
    exact IntermediateField.algebraMap_mem _ (⟨_, hK x.1 x.2⟩ : K)
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro x hx ih
    rw [Derivation.leibniz_inv, smul_eq_mul]
    exact mul_mem (neg_mem (pow_mem (inv_mem hx) 2)) ih
  · intro x y hx hy ihx ihy
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem hx ihy) (mul_mem hy ihx)

theorem solution {F G : Type*} [Field F] [Field G]
    [Differential G] [Algebra F G] [CharZero G] (K : IntermediateField F G)
    (hK : ∀ x ∈ K, x′ ∈ K) (hconst : constants G ⊆ (K : Set G)) {t : G}
    (htr : Transcendental K t)
    (hcase : (∃ s ∈ K, s ≠ 0 ∧ t′ = s′ / s) ∨ (∃ s ∈ K, t′ / t = s′))
    {h : G} (hh : h ∈ K)
    (hL : LiouvilleFormIn (IntermediateField.adjoin F (insert t (K : Set G)) : Set G) h) :
    LiouvilleFormIn (K : Set G) h := by
  classical
  letI : Differential K := subDiff K hK
  haveI : CharZero K := RingHom.charZero (algebraMap K G)
  have hcoeK : ∀ x : K, (((x′ : K)) : G) = (x : G)′ := fun x => rfl
  have htne : t ≠ 0 := fun h0 => htr (h0 ▸ isAlgebraic_zero)
  let M : IntermediateField K G := IntermediateField.adjoin K {t}
  have htM : t ∈ M := IntermediateField.subset_adjoin K _ rfl
  have ht'M : t′ ∈ M := by
    rcases hcase with ⟨s, hs, hs0, hts⟩ | ⟨s, hs, hts⟩
    · rw [hts]
      have h1 : s′ ∈ K := hK s hs
      exact M.div_mem (IntermediateField.algebraMap_mem M (⟨s′, h1⟩ : K))
        (IntermediateField.algebraMap_mem M (⟨s, hs⟩ : K))
    · have : t′ = s′ * t := by
        field_simp at hts
        rw [hts, mul_comm]
      rw [this]
      exact mul_mem (IntermediateField.algebraMap_mem M (⟨s′, hK s hs⟩ : K)) htM
  have hM : ∀ x ∈ M, x′ ∈ M := closed_adjoin K hK t ht'M
  letI : Differential M := subDiff M hM
  haveI : DifferentialAlgebra K M :=
    ⟨fun a => Subtype.ext rfl⟩
  let e : RatFunc K ≃ₐ[K] M := RatFunc.algEquivOfTranscendental t htr
  letI : Differential (RatFunc K) := Differential.equiv e.toRingEquiv
  haveI : DifferentialAlgebra K (RatFunc K) := DifferentialAlgebra.equiv e
  have he : ∀ x : RatFunc K, e (x′) = (e x)′ := fun x => by
    show e (e.symm _) = _
    simp
  have heG : ∀ x : RatFunc K, (((e (x′) : M)) : G) = ((e x : M) : G)′ := fun x => by
    rw [he]; rfl
  have heX : ((e RatFunc.X : M) : G) = t := by
    exact RatFunc.algEquivOfTranscendental_X t htr
  have hcon : ∀ x : RatFunc K, x′ = 0 → x ∈ Set.range (algebraMap K (RatFunc K)) := by
    intro x hx
    have h2 : ((e x : M) : G)′ = 0 := by
      rw [← heG, hx, map_zero]; rfl
    have hk : ((e x : M) : G) ∈ K := hconst h2
    refine ⟨⟨_, hk⟩, ?_⟩
    apply e.injective
    apply Subtype.val_injective
    rw [AlgEquiv.commutes]
    rfl
  have hLM : ∀ x ∈ IntermediateField.adjoin F (insert t (K : Set G)), x ∈ M := by
    have : IntermediateField.adjoin F (insert t (K : Set G)) ≤ M.restrictScalars F := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases hx with rfl | hx
      · exact htM
      · exact IntermediateField.algebraMap_mem M ⟨x, hx⟩
    exact fun x hx => this hx
  obtain ⟨n, c, u, v, hc, hu, hv, hfe⟩ := hL
  let cK : Fin n → K := fun i => ⟨c i, hconst (hc i)⟩
  let uQ : Fin n → RatFunc K := fun i => e.symm ⟨u i, hLM _ (hu i).1⟩
  let vQ : RatFunc K := e.symm ⟨v, hLM _ hv⟩
  let a : K := ⟨h, hh⟩
  have hcK : ∀ i, (cK i)′ = 0 := fun i => Subtype.ext (hc i)
  have huQ : ∀ i, uQ i ≠ 0 := by
    intro i h0
    apply (hu i).2
    have := congrArg (fun y => ((e y : M) : G)) h0
    simpa [uQ] using this
  have hfeQ : algebraMap K (RatFunc K) a =
      ∑ i, algebraMap K (RatFunc K) (cK i) * ((uQ i)′ / uQ i) + vQ′ := by
    apply e.injective
    apply Subtype.val_injective
    simp only [map_add, map_sum, map_mul, map_div₀, he, AlgEquiv.apply_symm_apply,
      AlgEquiv.commutes, uQ, vQ]
    push_cast
    exact hfe
  have key : ∃ (m : ℕ) (c' a' : Fin m → K) (b : K), (∀ i, (c' i)′ = 0) ∧ (∀ i, a' i ≠ 0) ∧
      a = ∑ i, c' i * ((a' i)′ / a' i) + b′ := by
    rcases hcase with ⟨s, hs, hs0, hts⟩ | ⟨s, hs, hts⟩
    · have hX : (RatFunc.X : RatFunc K)′ =
          algebraMap K (RatFunc K) ((⟨s, hs⟩ : K)′ / (⟨s, hs⟩ : K)) := by
        apply e.injective
        apply Subtype.val_injective
        rw [heG, heX, AlgEquiv.commutes, hts]
        rfl
      exact LiouvilleDiffAlg.ratFunc_descent_log (s := ⟨s, hs⟩)
        (fun h0 => hs0 (congrArg Subtype.val h0)) hX hcon cK hcK a uQ huQ vQ hfeQ
    · have hts' : t′ = s′ * t := by
        field_simp at hts
        rw [hts, mul_comm]
      have hX : (RatFunc.X : RatFunc K)′ =
          algebraMap K (RatFunc K) ((⟨s, hs⟩ : K)′) * RatFunc.X := by
        apply e.injective
        apply Subtype.val_injective
        rw [heG, heX, hts', map_mul, AlgEquiv.commutes]
        show s′ * t = s′ * ((e RatFunc.X : M) : G)
        rw [heX]
      exact LiouvilleDiffAlg.ratFunc_descent_exp (s := ⟨s, hs⟩)
        hX hcon cK hcK a uQ huQ vQ hfeQ
  obtain ⟨m, c', a', b, hc', ha', hfin⟩ := key
  have hG : h = ∑ i, (c' i : G) * ((a' i : G)′ / (a' i : G)) + (b : G)′ := by
    have := congrArg (fun y : K => (y : G)) hfin
    simpa [hcoeK] using this
  refine ⟨m, fun i => (c' i : G), fun i => (a' i : G), (b : G), ?_, ?_, b.2, hG⟩
  · intro i
    exact congrArg (fun y : K => (y : G)) (hc' i)
  · intro i
    exact ⟨(a' i).2, fun h0 => ha' i (Subtype.ext h0)⟩
