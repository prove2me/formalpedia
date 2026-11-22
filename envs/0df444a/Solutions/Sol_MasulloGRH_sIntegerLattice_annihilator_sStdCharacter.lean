-- Prove2me | solution 1 for MasulloGRH.sIntegerLattice_annihilator_sStdCharacter
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:52:39.761648+00:00
-- url     : https://prove2.me/submissions/0e476160-0c4c-487c-9d50-cfdb347d76d2

import Mathlib
import Definitions.Def_MasulloGRH_SLocalStandardCharacter

open NumberField IsDedekindDomain

set_option autoImplicit false

/-!
# The lattice of `S`-integers is its own annihilator for the standard character

The proof is elementary.  Write `Tr_∞ : F_∞ → ℝ` for the archimedean trace
`u ↦ ∑_w mult(w) Re(u_w)`, so that `Tr_∞(a) = Tr_{F/ℚ}(a)` for `a ∈ F`.

* Part 1: `ψ_S(x) = exp(-2πi Tr_∞(x_∞ - ξ))` for every `S`-integer `ξ` with `x_v - ξ ∈ 𝒪_v`
  (`v ∈ S_f`).
* Part 2: `(⇐)`, the trace dual of `𝒪_F` and the different, auxiliary valuation lemmas.
* Part 3: `(⇒)` from strong approximation and the description of the dual lattice of `𝒪_F`
  in `F_∞`.
* Part 4: the dual lattice of `𝒪_F` in `F_∞` consists of global elements.
* Part 5: strong approximation for `S`-integers (Chinese remainder theorem).
-/

namespace Sol_MasulloGRH_sIntegerLattice_annihilator_sStdCharacter

open MasulloGRH

variable {F : Type*} [Field F] [NumberField F]

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

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

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

section Part2

lemma exists_int_of_exp_eq_one (t : ℝ)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ)) = 1) : ∃ n : ℤ, t = n := by
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨-n, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h3 : (t : ℂ) = ((-n : ℤ) : ℂ) := by
    have h4 : (2 * Real.pi * Complex.I) * (t : ℂ) =
        (2 * Real.pi * Complex.I) * ((-n : ℤ) : ℂ) := by
      push_cast; linear_combination -hn
    exact mul_left_cancel₀ h2 h4
  exact_mod_cast h3

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

lemma mem_lattice_iff (y : SAdeleRing F Sf) :
    y ∈ sIntegerLattice Sf ↔ ∃ ξ ∈ SIntegers (F := F) Sf, sDiagonal Sf ξ = y := by
  unfold sIntegerLattice
  rw [AddSubgroup.mem_map]
  rfl

lemma algebraMap_int_mem (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
  exact v.valuation_le_one a

/-- (⇐) -/
lemma annihilates_of_mem (y : SAdeleRing F Sf) (hy : y ∈ sIntegerLattice Sf)
    (x : SAdeleRing F Sf) (hx : x ∈ sIntegerLattice Sf) :
    sStdCharacter Sf (x * y) = 1 := by
  obtain ⟨η, hη, rfl⟩ := (mem_lattice_iff Sf y).1 hy
  obtain ⟨ξ, hξ, rfl⟩ := (mem_lattice_iff Sf x).1 hx
  have hP : IsApprox Sf (sDiagonal Sf ξ * sDiagonal Sf η) (ξ * η) := by
    refine ⟨Subalgebra.mul_mem _ hξ hη, fun v => ?_⟩
    rw [map_mul, sub_self]
    exact zero_mem _
  rw [sStdCharacter_eq Sf _ _ hP, map_mul, sub_self]
  have h0 : ((0 : SAdeleRing F Sf)).1 = 0 := rfl
  rw [h0, trInf_zero]
  simp

lemma key_int (y : SAdeleRing F Sf)
    (hyp : ∀ x ∈ sIntegerLattice Sf, sStdCharacter Sf (x * y) = 1)
    (x : F) (hx : x ∈ SIntegers (F := F) Sf) (ξ : F)
    (hξ : IsApprox Sf (sDiagonal Sf x * y) ξ) :
    ∃ n : ℤ, trInf ((sDiagonal Sf x * y - sDiagonal Sf ξ).1) = n := by
  have h := hyp (sDiagonal Sf x) ((mem_lattice_iff Sf _).2 ⟨x, hx, rfl⟩)
  rw [sStdCharacter_eq Sf _ _ hξ] at h
  exact exists_int_of_exp_eq_one _ h

lemma IsApprox.int_mul {x' : SAdeleRing F Sf} {ξ : F} (h : IsApprox Sf x' ξ) (a : 𝓞 F) :
    IsApprox Sf (sDiagonal Sf (algebraMap (𝓞 F) F a) * x') (algebraMap (𝓞 F) F a * ξ) := by
  refine ⟨Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) h.1, fun v => ?_⟩
  have e : (sDiagonal Sf (algebraMap (𝓞 F) F a) * x' -
      sDiagonal Sf (algebraMap (𝓞 F) F a * ξ)).2 v =
      algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) (algebraMap (𝓞 F) F a) *
        (x' - sDiagonal Sf ξ).2 v := by
    simp only [map_mul, Prod.snd_sub, Prod.snd_mul, Pi.sub_apply, Pi.mul_apply, sDiagonal_snd]
    ring
  rw [e]
  exact mul_mem (algebraMap_int_mem _ a) (h.2 v)

lemma mul_mem_range_of_dual (ζ : F)
    (hζ : ∀ a : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (algebraMap (𝓞 F) F a * ζ) = n)
    (d : 𝓞 F) (hd : d ∈ differentIdeal ℤ (𝓞 F)) :
    algebraMap (𝓞 F) F d * ζ ∈ (algebraMap (𝓞 F) F).range := by
  have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := one_ne_zero
  have h1 : ζ ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    rw [FractionalIdeal.mem_one_iff] at ha
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨n, hn⟩ := hζ a'
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply, mul_comm, hn]
    simp
  have h2 : algebraMap (𝓞 F) F d ∈
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))⁻¹ := by
    rw [← coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  have h3 := FractionalIdeal.mul_mem_mul h2 h1
  rw [inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ h10),
    FractionalIdeal.mem_one_iff] at h3
  obtain ⟨c, hc⟩ := h3
  exact ⟨c, hc⟩

lemma valuation_le_one_of_dual (ζ : F)
    (hζ : ∀ a : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (algebraMap (𝓞 F) F a * ζ) = n)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) :
    v.valuation F ζ ≤ 1 := by
  rw [Ideal.dvd_iff_le] at hv
  obtain ⟨d, hd, hdv⟩ := SetLike.not_le_iff_exists.1 hv
  obtain ⟨c, hc⟩ := mul_mem_range_of_dual ζ hζ d hd
  have h1 : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hdv
  have h2 : v.valuation F (algebraMap (𝓞 F) F d * ζ) ≤ 1 := by
    rw [← hc]; exact v.valuation_le_one c
  rwa [map_mul, h1, one_mul] at h2

lemma exists_sInteger_valued_gt (SA : ∀ x : SAdeleRing F Sf, ∃ ξ, IsApprox Sf x ξ) (v₀ : Sf)
    (g : (v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) (hg : g ≠ 0) :
    ∃ x ∈ SIntegers (F := F) Sf,
      1 < Valued.v (algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) x * g) := by
  by_cases h : 1 < Valued.v g
  · exact ⟨1, Subalgebra.one_mem _, by simpa using h⟩
  · push_neg at h
    obtain ⟨π, hπ⟩ := (v₀ : HeightOneSpectrum (𝓞 F)).valuation_exists_uniformizer F
    have hπ' : Valued.v (algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) π) =
        WithZero.exp (-1 : ℤ) := by rw [valued_algebraMap, hπ]
    have hπ0 : algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) π ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hπ'
      exact WithZero.exp_ne_zero hπ'.symm
    have hg0 : Valued.v g ≠ 0 := (Valuation.ne_zero_iff _).2 hg
    have hc : 1 < Valued.v
        ((g * algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) π)⁻¹) := by
      rw [map_inv₀, map_mul, hπ']
      rw [one_lt_inv₀ (zero_lt_iff.2 (mul_ne_zero hg0 WithZero.exp_ne_zero))]
      calc Valued.v g * WithZero.exp (-1 : ℤ) ≤ 1 * WithZero.exp (-1 : ℤ) := by gcongr
        _ < 1 := by
          rw [one_mul, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    classical
    obtain ⟨x, hx1, hx2⟩ := SA (0, Pi.single v₀
      ((g * algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) π)⁻¹))
    have hx3 := hx2 v₀
    have e : (((0, Pi.single v₀
        ((g * algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) π)⁻¹)) -
        sDiagonal Sf x : SAdeleRing F Sf)).2 v₀ =
        (g * algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) π)⁻¹ -
          algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) x := by
      simp [sDiagonal_snd]
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers] at hx3
    have hx4 : Valued.v (algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) x) =
        Valued.v ((g * algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) π)⁻¹) := by
      have h5 := Valuation.map_sub_eq_of_lt_left Valued.v (lt_of_le_of_lt hx3 hc)
      rwa [sub_sub_cancel] at h5
    refine ⟨x, hx1, ?_⟩
    rw [map_mul, hx4, ← map_mul]
    have h6 : (g * algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) π)⁻¹ * g =
        (algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) π)⁻¹ := by
      field_simp
    rw [h6, map_inv₀, hπ', ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

end Part2

section Part3

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

lemma forward
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ Sf)
    (SA : ∀ x : SAdeleRing F Sf, ∃ ξ, IsApprox Sf x ξ)
    (D1 : ∀ z : InfiniteAdeleRing F,
      (∀ a : 𝓞 F, ∃ n : ℤ,
        trInf (algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F a) * z) = n) →
      ∃ ζ : F, algebraMap F (InfiniteAdeleRing F) ζ = z)
    (y : SAdeleRing F Sf)
    (hyp : ∀ x ∈ sIntegerLattice Sf, sStdCharacter Sf (x * y) = 1) :
    y ∈ sIntegerLattice Sf := by
  -- Step 1: approximate `y`
  obtain ⟨η, hη⟩ := SA y
  -- Step 2: the archimedean part of `y - η` pairs integrally with `𝓞 F`
  have h2 : ∀ a : 𝓞 F, ∃ n : ℤ, trInf (algebraMap F (InfiniteAdeleRing F)
      (algebraMap (𝓞 F) F a) * (y - sDiagonal Sf η).1) = n := by
    intro a
    obtain ⟨n, hn⟩ := key_int Sf y hyp _ (Subalgebra.algebraMap_mem _ a) _ (hη.int_mul Sf a)
    refine ⟨n, ?_⟩
    rw [← hn]
    congr 1
    simp only [map_mul, Prod.fst_sub, Prod.fst_mul, sDiagonal_fst]
    ring
  -- Step 3: it is a global element `ζ` of the dual lattice
  obtain ⟨ζ, hζ⟩ := D1 _ h2
  have h3 : ∀ a : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (algebraMap (𝓞 F) F a * ζ) = n := by
    intro a
    obtain ⟨n, hn⟩ := h2 a
    refine ⟨n, ?_⟩
    rw [← hζ, ← map_mul, trInf_algebraMap] at hn
    exact_mod_cast hn
  -- Step 4: `ζ` is an `S`-integer
  have hζS : ζ ∈ SIntegers (F := F) Sf := fun v hv =>
    valuation_le_one_of_dual ζ h3 v (fun hdiv => hv (hS v hdiv))
  -- Step 5
  have hθS : η + ζ ∈ SIntegers (F := F) Sf := Subalgebra.add_mem _ hη.1 hζS
  have hy1 : y.1 = algebraMap F (InfiniteAdeleRing F) (η + ζ) := by
    have h4 : (y - sDiagonal Sf η).1 = y.1 - algebraMap F (InfiniteAdeleRing F) η := rfl
    rw [h4] at hζ
    rw [map_add, hζ]; ring
  have hdual : ∀ (x : F), x ∈ SIntegers (F := F) Sf → ∀ ξ : F,
      IsApprox Sf (sDiagonal Sf x * y) ξ →
      ∀ a : 𝓞 F, ∃ n : ℤ,
        Algebra.trace ℚ F (algebraMap (𝓞 F) F a * (ξ - x * (η + ζ))) = n := by
    intro x hx ξ hξ a
    have hap := hξ.int_mul Sf a
    rw [← mul_assoc, ← map_mul] at hap
    obtain ⟨n, hn⟩ := key_int Sf y hyp _
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) hx) _ hap
    refine ⟨-n, ?_⟩
    have e : (sDiagonal Sf (algebraMap (𝓞 F) F a * x) * y -
        sDiagonal Sf (algebraMap (𝓞 F) F a * ξ)).1 =
        algebraMap F (InfiniteAdeleRing F)
          (-(algebraMap (𝓞 F) F a * (ξ - x * (η + ζ)))) := by
      simp only [Prod.fst_sub, Prod.fst_mul, sDiagonal_fst, hy1, map_mul, map_sub, map_neg,
        map_add]
      ring
    rw [e, trInf_algebraMap, map_neg] at hn
    have h5 : ((Algebra.trace ℚ F (algebraMap (𝓞 F) F a * (ξ - x * (η + ζ))) : ℚ) : ℝ) =
        ((-n : ℤ) : ℝ) := by
      push_cast at hn ⊢; linarith
    exact_mod_cast h5
  have hy2 : ∀ v : Sf, y.2 v =
      algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) (η + ζ) := by
    by_contra hne
    push_neg at hne
    obtain ⟨v₀, hv₀⟩ := hne
    obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
    have ht0 : y.2 v₀ -
        algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) (η + ζ) ≠ 0 :=
      sub_ne_zero.2 hv₀
    have hd'0 : algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F)
        (algebraMap (𝓞 F) F d) ≠ 0 := by
      rw [Ne, map_eq_zero, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)]
      exact hd0
    obtain ⟨x, hx, hxgt⟩ := exists_sInteger_valued_gt Sf SA v₀ _ (mul_ne_zero hd'0 ht0)
    obtain ⟨ξ, hξ⟩ := SA (sDiagonal Sf x * y)
    obtain ⟨c, hc⟩ := mul_mem_range_of_dual _ (hdual x hx ξ hξ) d hd
    have hle : Valued.v (algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F)
        (algebraMap (𝓞 F) F d) *
        algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F)
          (ξ - x * (η + ζ))) ≤ 1 := by
      rw [← map_mul, ← hc]
      exact algebraMap_int_mem _ c
    have hd'le : Valued.v (algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F)
        (algebraMap (𝓞 F) F d)) ≤ 1 := algebraMap_int_mem _ d
    have hxt : 1 < Valued.v (algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) x *
        (y.2 v₀ -
          algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) (η + ζ))) := by
      refine lt_of_lt_of_le hxgt ?_
      rw [mul_left_comm, map_mul]
      calc _ ≤ 1 * Valued.v
            (algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) x *
              (y.2 v₀ -
                algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) (η + ζ))) := by
            gcongr
        _ = _ := one_mul _
    have happ := hξ.2 v₀
    have e : (sDiagonal Sf x * y - sDiagonal Sf ξ).2 v₀ =
        algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) x *
          (y.2 v₀ -
            algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) (η + ζ)) -
        algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F)
          (ξ - x * (η + ζ)) := by
      simp only [Prod.snd_sub, Prod.snd_mul, Pi.sub_apply, Pi.mul_apply, sDiagonal_snd, map_sub,
        map_mul, map_add]
      ring
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers] at happ
    have heq := Valuation.map_sub_eq_of_lt_left Valued.v (lt_of_le_of_lt happ hxt)
    rw [sub_sub_cancel] at heq
    rw [map_mul, heq, ← map_mul, mul_left_comm] at hle
    exact absurd hle (not_le.2 hxgt)
  refine (mem_lattice_iff Sf y).2 ⟨η + ζ, hθS, ?_⟩
  refine Prod.ext hy1.symm (funext fun v => ?_)
  rw [hy2 v]
  rfl

end Part3

section Part4

open scoped Classical in
/-- The trace form on the mixed space `ℝ^{r₁} × ℂ^{r₂}`. -/
noncomputable def tauMixed : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ where
  toFun x := ∑ w : {w : InfinitePlace F // w.IsReal}, x.1 w +
    ∑ w : {w : InfinitePlace F // w.IsComplex}, 2 * (x.2 w).re
  map_add' x x' := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.add_re, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.re_ofReal_mul, Finset.mul_sum, mul_add, RingHom.id_apply]
    congr 1
    refine Finset.sum_congr rfl fun w _ => by ring

open scoped Classical in
lemma trInf_eq_tauMixed (u : InfiniteAdeleRing F) :
    trInf u = tauMixed (InfiniteAdeleRing.ringEquiv_mixedSpace F u) := by
  unfold trInf
  rw [InfinitePlace.sum_eq_sum_add_sum, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [tauMixed, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul,
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2, Complex.ofReal_re]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [InfinitePlace.mult_isComplex, Nat.cast_ofNat]

lemma tauMixed_mixedEmbedding (a : F) :
    tauMixed (mixedEmbedding F a) = ((Algebra.trace ℚ F a : ℚ) : ℝ) := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, ← trInf_eq_tauMixed, trInf_algebraMap]

lemma trInf_mul_sum (a : F) (z : InfiniteAdeleRing F) :
    trInf (algebraMap F (InfiniteAdeleRing F) a * z) =
      ∑ i, ((mixedEmbedding.latticeBasis F).equivFun
          (InfiniteAdeleRing.ringEquiv_mixedSpace F z) i) *
        ((Algebra.trace ℚ F (a * integralBasis F i) : ℚ) : ℝ) := by
  rw [trInf_eq_tauMixed, map_mul, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  conv_lhs => rw [← (mixedEmbedding.latticeBasis F).sum_equivFun
    (InfiniteAdeleRing.ringEquiv_mixedSpace F z)]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, mixedEmbedding.latticeBasis_apply, ← map_mul,
    tauMixed_mixedEmbedding]

/-- The dual lattice of `𝓞 F` in `F_∞` consists of global elements. -/
lemma exists_global_of_dual (z : InfiniteAdeleRing F)
    (hz : ∀ a : 𝓞 F, ∃ n : ℤ,
      trInf (algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F a) * z) = n) :
    ∃ ζ : F, algebraMap F (InfiniteAdeleRing F) ζ = z := by
  classical
  choose m hm using fun j : Module.Free.ChooseBasisIndex ℤ (𝓞 F) =>
    hz (RingOfIntegers.basis F j)
  let c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ :=
    (mixedEmbedding.latticeBasis F).equivFun (InfiniteAdeleRing.ringEquiv_mixedSpace F z)
  let G : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) ℚ :=
    Algebra.traceMatrix ℚ (integralBasis F)
  have hdet : G.det ≠ 0 := Algebra.discr_not_zero_of_basis ℚ (integralBasis F)
  have hsys : (G.map (algebraMap ℚ ℝ)).mulVec c = fun j => (m j : ℝ) := by
    funext j
    rw [← hm j, ← integralBasis_apply, trInf_mul_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    rfl
  let q : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℚ := G⁻¹.mulVec (fun j => (m j : ℚ))
  have hq : G.mulVec q = fun j => (m j : ℚ) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec]
  have hq' : (G.map (algebraMap ℚ ℝ)).mulVec (fun i => ((q i : ℚ) : ℝ)) =
      fun j => (m j : ℝ) := by
    funext j
    have h := RingHom.map_mulVec (algebraMap ℚ ℝ) G q j
    rw [hq] at h
    rw [show (fun i => ((q i : ℚ) : ℝ)) = (algebraMap ℚ ℝ) ∘ q from rfl, ← h]
    simp
  have hdet' : (G.map (algebraMap ℚ ℝ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using hdet
  have hcq : c = fun i => ((q i : ℚ) : ℝ) := by
    have h0 : (G.map (algebraMap ℚ ℝ)).mulVec (c - fun i => ((q i : ℚ) : ℝ)) = 0 := by
      rw [Matrix.mulVec_sub, hsys, hq', sub_self]
    exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero hdet' h0)
  refine ⟨∑ i, q i • integralBasis F i, ?_⟩
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
  rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, map_sum]
  conv_rhs => rw [← (mixedEmbedding.latticeBasis F).sum_equivFun
    (InfiniteAdeleRing.ringEquiv_mixedSpace F z)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (mixedEmbedding.latticeBasis F).equivFun
      (InfiniteAdeleRing.ringEquiv_mixedSpace F z) i = ((q i : ℚ) : ℝ) := congrFun hcq i
  rw [map_rat_smul, mixedEmbedding.latticeBasis_apply, h1, Rat.cast_smul_eq_qsmul]

end Part4

section Part5

lemma exists_local_approx (v : HeightOneSpectrum (𝓞 F)) (t : v.adicCompletion F) :
    ∃ a : F, t - algebraMap F (v.adicCompletion F) a ∈ v.adicCompletionIntegers F := by
  have hopen : IsOpen {y : v.adicCompletion F | t - y ∈ v.adicCompletionIntegers F} :=
    (Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage
      (continuous_const.sub continuous_id)
  have hne : {y : v.adicCompletion F | t - y ∈ v.adicCompletionIntegers F}.Nonempty := by
    refine ⟨t, ?_⟩
    show t - t ∈ v.adicCompletionIntegers F
    rw [sub_self]
    exact zero_mem _
  exact (HeightOneSpectrum.denseRange_algebraMap (v := v) (K := F)).exists_mem_open hopen hne

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

/-- Strong approximation: every `S`-adele is congruent to an `S`-integer modulo
`∏_{v ∈ S_f} 𝒪_v`. -/
lemma strong_approx (x : SAdeleRing F Sf) : ∃ ξ, IsApprox Sf x ξ := by
  classical
  choose a ha using fun v : Sf => exists_local_approx (v : HeightOneSpectrum (𝓞 F)) (x.2 v)
  obtain ⟨⟨d, hdmem⟩, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F))
    (Finset.univ : Finset Sf) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdmem
  choose r hr using fun v : Sf => hd v (Finset.mem_univ v)
  have hr' : ∀ v : Sf, algebraMap (𝓞 F) F (r v) = algebraMap (𝓞 F) F d * a v := fun v => by
    rw [hr v, Algebra.smul_def]
  choose n hn using fun w : HeightOneSpectrum (𝓞 F) =>
    (⟨_, w.intValuation_if_neg hd0⟩ : ∃ n : ℕ, w.intValuation d = WithZero.exp (-(n : ℤ)))
  have hfin : {w : HeightOneSpectrum (𝓞 F) | w.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by simpa using hd0)
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Sf ∪ hfin.toFinset)
    (fun w => w.asIdeal) n
    (fun w _ => w.prime) (fun w _ w' _ hww' h => hww' (HeightOneSpectrum.ext h))
    (fun w => if h : (w : HeightOneSpectrum (𝓞 F)) ∈ Sf then r ⟨w, h⟩ else 0)
  have hcS : ∀ v : Sf, (v : HeightOneSpectrum (𝓞 F)).intValuation (c - r v) ≤
      (v : HeightOneSpectrum (𝓞 F)).intValuation d := by
    intro v
    have h := hc v (Finset.mem_union_left _ v.2)
    dsimp only at h
    rw [dif_pos v.2] at h
    rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact h
  have hcT : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ Sf → w.intValuation c ≤ w.intValuation d := by
    intro w hw
    by_cases hwT : w ∈ Sf ∪ hfin.toFinset
    · have h := hc w hwT
      dsimp only at h
      rw [dif_neg hw, sub_zero] at h
      rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem]
      exact h
    · have hwd : ¬ w.asIdeal ∣ Ideal.span {d} := fun hdiv =>
        hwT (Finset.mem_union_right _ (hfin.mem_toFinset.2 hdiv))
      have h1 : w.intValuation d = 1 := by
        rw [Ideal.dvd_span_singleton, ← HeightOneSpectrum.intValuation_lt_one_iff_mem,
          not_lt] at hwd
        exact le_antisymm (w.intValuation_le_one d) hwd
      rw [h1]
      exact w.intValuation_le_one c
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)]
    exact hd0
  have hpos : ∀ w : HeightOneSpectrum (𝓞 F), 0 < w.intValuation d := fun w =>
    zero_lt_iff.2 (w.intValuation_ne_zero d hd0)
  refine ⟨algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F d, ?_, ?_⟩
  · intro w hw
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact (div_le_one₀ (hpos w)).2 (hcT w hw)
  · intro v
    have e : (x - sDiagonal Sf (algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F d)).2 v =
        (x.2 v - algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) (a v)) +
          algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
            (algebraMap (𝓞 F) F (r v - c) / algebraMap (𝓞 F) F d) := by
      have h1 : algebraMap (𝓞 F) F (r v - c) / algebraMap (𝓞 F) F d =
          a v - algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F d := by
        rw [map_sub, hr' v]
        field_simp
      rw [h1]
      simp only [Prod.snd_sub, Pi.sub_apply, sDiagonal_snd, map_sub]
      ring
    rw [e]
    refine add_mem (ha v) ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap, map_div₀,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      Valuation.map_sub_swap]
    exact (div_le_one₀ (hpos _)).2 (hcS v)

end Part5

end Sol_MasulloGRH_sIntegerLattice_annihilator_sStdCharacter

open MasulloGRH Sol_MasulloGRH_sIntegerLattice_annihilator_sStdCharacter in
theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ Sf)
    (y : SAdeleRing F Sf) :
    (∀ x ∈ sIntegerLattice Sf, sStdCharacter Sf (x * y) = 1) ↔ y ∈ sIntegerLattice Sf := by
  constructor
  · intro hyp
    exact forward Sf hS (strong_approx Sf) exists_global_of_dual y hyp
  · intro hy x hx
    exact annihilates_of_mem Sf y hy x hx
