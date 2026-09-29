-- Prove2me | solution 1 for Ihara.hasTrivialSchurMultiplier_SL2_ZMod_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/41e7eb58-d223-5f39-9dd3-3213e721d205

import Mathlib
import Definitions.Def_SchurMultiplierTrivial
import Theorems.Thm_Ihara_hasTrivialSchurMultiplier_of_sylow
import Theorems.Thm_Ihara_hasTrivialSchurMultiplier_of_dicyclic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_of_prime

open scoped MatrixGroups
open Matrix

namespace IharaSchurSL2

section MatrixFacts

variable {F : Type*} [Field F]

def wSL : SL(2, F) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

@[scoped simp] theorem coe_wSL : ((wSL : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := rfl

theorem coe_wSL_sq : (((wSL : SL(2, F)) ^ 2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_wSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem wSL_conj_of_symm (x : SL(2, F))
    (hx : (x : Matrix (Fin 2) (Fin 2) F) 0 1 = (x : Matrix (Fin 2) (Fin 2) F) 1 0) :
    wSL * x * wSL⁻¹ = x⁻¹ := by
  apply Subtype.ext
  obtain ⟨a, b, c, d, hM⟩ :
      ∃ a b c d : F, (x : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hM] at hx
  have hbc : b = c := by simpa using hx
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, coe_wSL, hM,
    Matrix.adjugate_fin_two_of, Matrix.adjugate_fin_two_of]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hbc]

theorem coe_eq_neg_one_of_orderOf_eq_two (h2 : (2 : F) ≠ 0) (g : SL(2, F))
    (hg : orderOf g = 2) : (g : Matrix (Fin 2) (Fin 2) F) = -1 := by
  have hsq : (g : Matrix (Fin 2) (Fin 2) F) * g = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg, pow_two] at this
    simpa using congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) this
  have hne : g ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hg; exact absurd hg (by norm_num)
  set a := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (g : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have hM : (g : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := Matrix.eta_fin_two _
  have hdet : a * d - b * c = 1 := by
    have := g.2; rw [hM, Matrix.det_fin_two_of] at this; exact this
  rw [hM] at hsq
  have e00 : a * a + b * c = 1 := by
    have := congrFun (congrFun hsq 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e01 : a * b + b * d = 0 := by
    have := congrFun (congrFun hsq 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e10 : c * a + d * c = 0 := by
    have := congrFun (congrFun hsq 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e11 : c * b + d * d = 1 := by
    have := congrFun (congrFun hsq 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this

  have htr : a + d ≠ 0 := by
    intro h0
    have hd' : d = -a := by linear_combination h0
    have : (2 : F) = 0 := by linear_combination -e00 - hdet + a * h0
    exact h2 this
  have hb0 : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination e01
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h htr
  have hc0 : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination e10
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h htr
  have h1 : a * a = 1 := by rw [hb0] at e00; linear_combination e00
  have had : a = d := by

    linear_combination (-a) * hdet + d * h1 - a * c * hb0

  have ha' : a = 1 ∨ a = -1 := by
    have : (a - 1) * (a + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases ha' with h | h
  · exfalso; apply hne
    apply Subtype.ext
    rw [hM, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb0, hc0, ← had, h]
  · rw [hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb0, hc0, ← had, h]

theorem symm_of_commute (h2 : (2 : F) ≠ 0) {a₀ b₀ : F} (h0 : a₀ ≠ 0 ∨ b₀ ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) F) (hM : M * !![a₀, b₀; b₀, -a₀] = !![a₀, b₀; b₀, -a₀] * M) :
    M 0 1 = M 1 0 := by
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10

  have hb : b₀ * (M 0 1 - M 1 0) = 0 := by linear_combination e00
  have ha : 2 * a₀ * (M 0 1 - M 1 0) = 0 := by linear_combination -e01 - e10
  rcases h0 with ha0 | hb0
  · have := mul_eq_zero.mp ha
    rcases this with h | h
    · exact absurd h (mul_ne_zero h2 ha0)
    · linear_combination h
  · rcases mul_eq_zero.mp hb with h | h
    · exact absurd h hb0
    · linear_combination h

end MatrixFacts

section Card

variable {F : Type*} [Field F]

theorem det_GL2_surjective :
    Function.Surjective
      (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ) := by
  intro u
  refine ⟨Matrix.GeneralLinearGroup.mk' !![(u : F), 0; 0, 1] ?_, ?_⟩
  · simp only [Matrix.det_fin_two_of, mul_one, sub_zero, mul_zero]
    exact Units.invertible u
  · ext
    simp [Matrix.det_fin_two_of]

theorem card_ker_det_GL2 :
    Nat.card (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker = Nat.card (SL(2, F)) := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun A : SL(2, F) =>
      (⟨(A : GL (Fin 2) F), by
        rw [MonoidHom.mem_ker]
        exact Matrix.SpecialLinearGroup.coeToGL_det A⟩ :
        (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker))
    ⟨?_, ?_⟩)).symm
  · intro A B h
    have h' := congrArg Subtype.val h
    exact Matrix.SpecialLinearGroup.toGL_injective h'
  · rintro ⟨g, hg⟩
    rw [MonoidHom.mem_ker] at hg
    refine ⟨⟨(g : Matrix (Fin 2) (Fin 2) F), ?_⟩, ?_⟩
    · have := congrArg Units.val hg
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    · apply Subtype.ext
      ext i j
      rfl

variable [Fintype F]

theorem card_SL2 :
    Nat.card (SL(2, F)) = Fintype.card F * ((Fintype.card F - 1) * (Fintype.card F + 1)) := by
  classical
  have h1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hGL : Nat.card (GL (Fin 2) F) =
      (Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 2 - Fintype.card F) := by
    rw [Matrix.card_GL_field 2]
    simp [Fin.prod_univ_two]
  have hprod : Nat.card (GL (Fin 2) F) = Nat.card (SL(2, F)) * Nat.card Fˣ := by
    rw [← card_ker_det_GL2 (F := F)]
    have e := QuotientGroup.quotientKerEquivOfSurjective _ (det_GL2_surjective (F := F))
    rw [← Nat.card_congr e.toEquiv, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hunits : Nat.card Fˣ = Fintype.card F - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
  rw [hGL, hunits] at hprod
  generalize Fintype.card F = q at *
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have e1 : (r + 2) ^ 2 - 1 = (r + 1) * (r + 3) := by
    rw [show (r + 2) ^ 2 = (r + 1) * (r + 3) + 1 by ring, Nat.add_sub_cancel]
  have e2 : (r + 2) ^ 2 - (r + 2) = (r + 2) * (r + 1) := by
    rw [show (r + 2) ^ 2 = (r + 2) * (r + 1) + (r + 2) by ring, Nat.add_sub_cancel]
  have e3 : r + 2 - 1 = r + 1 := rfl
  rw [e1, e2, e3] at hprod
  rw [e3]
  have key : Nat.card (SL(2, F)) * (r + 1) = (r + 2) * ((r + 1) * (r + 2 + 1)) * (r + 1) := by
    rw [← hprod]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos r) key

end Card

theorem exists_orderOf_eq_of_injective {C H : Type*} [Group C] [Finite C] [IsCyclic C]
    [Group H] (ψ : C →* H) (hψ : Function.Injective ψ) {n : ℕ} (hn : n ∣ Nat.card C) :
    ∃ c : C, orderOf (ψ c) = n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C)
  refine ⟨g ^ (Nat.card C / n), ?_⟩
  rw [orderOf_injective ψ hψ, ← hg]
  exact orderOf_pow_orderOf_div (hg ▸ Nat.card_pos.ne') (hg ▸ hn)

section SplitTorus

variable {F : Type*} [Field F]

def diagSL : Fˣ →* SL(2, F) where
  toFun t := ⟨!![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two_of]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' s t := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

@[scoped simp] theorem coe_diagSL (t : Fˣ) :
    ((diagSL t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)] :=
  rfl

theorem diagSL_injective : Function.Injective (diagSL : Fˣ →* SL(2, F)) := by
  intro s t h
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  exact Units.ext (by simpa using this)

theorem split_torus_supply [Finite F] {n : ℕ} (hn : n ∣ Nat.card F - 1) :
    ∃ x : SL(2, F), orderOf x = n ∧
      (x : Matrix (Fin 2) (Fin 2) F) 0 1 = (x : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  have hc : n ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨c, hc⟩ := exists_orderOf_eq_of_injective diagSL diagSL_injective hc
  exact ⟨diagSL c, hc, by simp⟩

end SplitTorus

section NonsplitTorus

open Polynomial

variable {F : Type*} [Field F] (f : F[X]) (R : Matrix (Fin 2) (Fin 2) F)
  (hR : Polynomial.aeval R f = 0)

noncomputable def evalHom : AdjoinRoot f →+* Matrix (Fin 2) (Fin 2) F :=
  Ideal.Quotient.lift (Ideal.span {f}) (Polynomial.aeval R).toRingHom (by
    intro g hg
    obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hg
    simp [hR])

theorem evalHom_mk (g : F[X]) : evalHom f R hR (AdjoinRoot.mk f g) = Polynomial.aeval R g :=
  Ideal.Quotient.lift_mk _ _ _

theorem evalHom_root : evalHom f R hR (AdjoinRoot.root f) = R := by
  rw [← AdjoinRoot.mk_X, evalHom_mk, Polynomial.aeval_X]

theorem evalHom_comm (z : AdjoinRoot f) : evalHom f R hR z * R = R * evalHom f R hR z := by
  have h := evalHom_root f R hR
  have : evalHom f R hR (z * AdjoinRoot.root f) = evalHom f R hR (AdjoinRoot.root f * z) := by
    rw [mul_comm]
  rwa [map_mul, map_mul, h] at this

theorem finite_adjoinRoot [Finite F] (hf0 : f ≠ 0) : Finite (AdjoinRoot f) := by
  haveI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  exact Module.finite_of_finite F

noncomputable def detHom : (AdjoinRoot f)ˣ →* Fˣ :=
  Units.map (Matrix.detMonoidHom.comp (evalHom f R hR).toMonoidHom)

@[scoped simp] theorem val_detHom_apply (z : (AdjoinRoot f)ˣ) :
    ((detHom f R hR z : Fˣ) : F) = (evalHom f R hR (z : AdjoinRoot f)).det := rfl

noncomputable def normOneHom : (detHom f R hR).ker →* SL(2, F) where
  toFun z := ⟨evalHom f R hR ((z : (AdjoinRoot f)ˣ) : AdjoinRoot f), by
    have h := congrArg Units.val (MonoidHom.mem_ker.mp z.2)
    simpa using h⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_normOneHom (z : (detHom f R hR).ker) :
    ((normOneHom f R hR z : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
      = evalHom f R hR ((z : (AdjoinRoot f)ˣ) : AdjoinRoot f) := rfl

theorem normOneHom_injective [Fact (Irreducible f)] :
    Function.Injective (normOneHom f R hR) := by
  intro a b h
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h
  exact Subtype.ext (Units.ext ((evalHom f R hR).injective this))

theorem succ_card_dvd_card_ker_detHom [Fintype F] [Fact (Irreducible f)]
    (hf2 : f.natDegree = 2) :
    (Fintype.card F + 1) ∣ Nat.card (detHom f R hR).ker := by
  classical
  have hf0 : f ≠ 0 := (Fact.out : Irreducible f).ne_zero
  haveI : Finite (AdjoinRoot f) := finite_adjoinRoot f hf0
  have hcardK : Nat.card (AdjoinRoot f) = Fintype.card F ^ 2 := by
    have b := (AdjoinRoot.powerBasis hf0).basis
    rw [Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_fin, AdjoinRoot.powerBasis_dim, hf2]
  set δ := detHom f R hR
  have h1 : Nat.card δ.ker * Nat.card δ.range = Fintype.card F ^ 2 - 1 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, Nat.card_units, hcardK]
  have h2 : Nat.card δ.range ∣ Fintype.card F - 1 := by
    have := Subgroup.card_subgroup_dvd_card δ.range
    rwa [Nat.card_units, Nat.card_eq_fintype_card (α := F)] at this
  have hr0 : 0 < Nat.card δ.range := Nat.card_pos
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  generalize Fintype.card F = q at h1 h2 hq ⊢
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rw [show (r + 1) ^ 2 - 1 = r * (r + 1 + 1) by
    rw [show (r + 1) ^ 2 = r * (r + 1 + 1) + 1 by ring, Nat.add_sub_cancel]] at h1
  rw [Nat.add_sub_cancel] at h2
  obtain ⟨s, hs⟩ := h2
  refine ⟨s, Nat.eq_of_mul_eq_mul_right hr0 ?_⟩
  rw [h1]
  subst hs
  ring

theorem nonsplit_torus_supply [Fintype F] (h2 : ringChar F ≠ 2) {n : ℕ}
    (hn : n ∣ Fintype.card F + 1) :
    ∃ x : SL(2, F), orderOf x = n ∧
      (x : Matrix (Fin 2) (Fin 2) F) 0 1 = (x : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  classical
  have h2' : (2 : F) ≠ 0 := Ring.two_ne_zero h2

  obtain ⟨d, hd⟩ := FiniteField.exists_nonsquare h2
  have hd0 : d ≠ 0 := by rintro rfl; exact hd IsSquare.zero
  obtain ⟨a₀, b₀, hab⟩ : ∃ a₀ b₀ : F, a₀ ^ 2 + b₀ ^ 2 = d := by
    obtain ⟨a, b, h⟩ := FiniteField.exists_root_sum_quadratic (f := X ^ 2) (g := X ^ 2 - C d)
      (degree_X_pow 2) (degree_X_pow_sub_C (by norm_num) d)
      (FiniteField.odd_card_of_char_ne_two h2)
    refine ⟨a, b, ?_⟩
    simp only [eval_pow, eval_X, eval_sub, eval_C] at h
    linear_combination h
  have h0 : a₀ ≠ 0 ∨ b₀ ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply hd0
    rw [← hab, h.1, h.2]
    ring

  set R : Matrix (Fin 2) (Fin 2) F := !![a₀, b₀; b₀, -a₀] with hRdef
  have hRsq : R * R = d • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hRdef, Matrix.mul_fin_two, ← hab]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

  set f : F[X] := X ^ 2 - C d with hfdef
  have hfd : f.natDegree = 2 := natDegree_X_pow_sub_C
  have hf0 : f ≠ 0 := (monic_X_pow_sub_C d two_ne_zero).ne_zero
  have hirr : Irreducible f := by
    rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
      Multiset.eq_zero_iff_forall_notMem]
    intro a ha
    rw [mem_roots hf0, IsRoot.def, hfdef, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at ha
    exact hd ⟨a, by rw [← ha, sq]⟩
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  haveI : Finite (AdjoinRoot f) := finite_adjoinRoot f hf0
  have hR : Polynomial.aeval R f = 0 := by
    rw [hfdef, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, pow_two, hRsq,
      Algebra.algebraMap_eq_smul_one, sub_self]

  have hN := succ_card_dvd_card_ker_detHom f R hR hfd
  obtain ⟨c, hc⟩ := exists_orderOf_eq_of_injective (normOneHom f R hR)
    (normOneHom_injective f R hR) (hn.trans hN)
  exact ⟨normOneHom f R hR c, hc, symm_of_commute h2' h0 _ (evalHom_comm f R hR _)⟩

end NonsplitTorus

section Dicyclic

variable {G : Type*} [Group G]

theorem card_closure_pair_of_conj_inv {x w : G} (hw : w * x * w⁻¹ = x⁻¹)
    (hw2 : w ^ 2 ∈ Subgroup.zpowers x) (hwn : w ∉ Subgroup.zpowers x) :
    Nat.card (Subgroup.closure ({x, w} : Set G)) = orderOf x * 2 := by
  classical
  set Q := Subgroup.closure ({x, w} : Set G) with hQ
  have hxQ : x ∈ Q := Subgroup.subset_closure (by simp)
  have hwQ : w ∈ Q := Subgroup.subset_closure (by simp)
  have hw' : w⁻¹ * x * w = x⁻¹ := by
    have h1 : w⁻¹ * x⁻¹ * w = x := by
      calc w⁻¹ * x⁻¹ * w = w⁻¹ * (w * x * w⁻¹) * w := by rw [hw]
        _ = x := by group
    calc w⁻¹ * x * w = (w⁻¹ * x⁻¹ * w)⁻¹ := by group
      _ = x⁻¹ := by rw [h1]

  have hnorm : ∀ g ∈ Q, ∀ y ∈ Subgroup.zpowers x,
      g * y * g⁻¹ ∈ Subgroup.zpowers x ∧ g⁻¹ * y * g ∈ Subgroup.zpowers x := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => ∀ y ∈ Subgroup.zpowers x,
      g * y * g⁻¹ ∈ Subgroup.zpowers x ∧ g⁻¹ * y * g ∈ Subgroup.zpowers x)
      ?_ ?_ ?_ ?_ hg
    · rintro g hg y ⟨k, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      dsimp only
      rcases hg with hg | hg <;> rw [hg]
      · rw [show x * x ^ k * x⁻¹ = x ^ k by group, show x⁻¹ * x ^ k * x = x ^ k by group]
        exact ⟨Subgroup.zpow_mem_zpowers x k, Subgroup.zpow_mem_zpowers x k⟩
      · have e1 : w * x ^ k * w⁻¹ = x⁻¹ ^ k := by rw [← conj_zpow, hw]
        have e2 : w⁻¹ * x ^ k * w = x⁻¹ ^ k := by
          rw [← hw', show w⁻¹ * x * w = w⁻¹ * x * w⁻¹⁻¹ by rw [inv_inv], conj_zpow, inv_inv]
        rw [e1, e2]
        exact ⟨Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) k,
          Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) k⟩
    · intro y hy
      simpa using hy
    · intro a b _ _ ha hb y hy
      obtain ⟨hb1, _⟩ := hb y hy
      obtain ⟨ha1, _⟩ := ha _ hb1
      obtain ⟨_, ha2⟩ := ha y hy
      obtain ⟨_, hb2⟩ := hb _ ha2
      constructor
      · simpa [mul_assoc] using ha1
      · simpa [mul_assoc] using hb2
    · intro a _ ha y hy
      obtain ⟨ha1, ha2⟩ := ha y hy
      exact ⟨by simpa using ha2, by simpa using ha1⟩

  set H : Subgroup Q := (Subgroup.zpowers x).subgroupOf Q with hH
  haveI hHn : H.Normal := by
    refine ⟨fun y hy g => ?_⟩
    rw [hH, Subgroup.mem_subgroupOf] at hy ⊢
    simpa using (hnorm g g.2 _ hy).1
  have hHcard : Nat.card H = orderOf x := by
    rw [hH, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxQ)).toEquiv,
      Nat.card_zpowers]

  have hHidx : H.index = 2 := by
    rw [Subgroup.index_eq_card]
    set wq : Q ⧸ H := QuotientGroup.mk ⟨w, hwQ⟩ with hwq
    have hgen : Subgroup.zpowers wq = ⊤ := by
      have htop : Subgroup.map (QuotientGroup.mk' H) ⊤ = ⊤ :=
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective H)
      rw [← Subgroup.closure_closure_coe_preimage (k := ({x, w} : Set G)),
        MonoidHom.map_closure] at htop
      rw [eq_top_iff, ← htop, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg
      · have : (QuotientGroup.mk' H) g = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hH, Subgroup.mem_subgroupOf, hg]
          exact Subgroup.mem_zpowers x
        rw [this]
        exact one_mem _
      · have : (QuotientGroup.mk' H) g = wq := by
          rw [QuotientGroup.mk'_apply, hwq]
          congr 1
          exact Subtype.ext hg
        rw [this]
        exact Subgroup.mem_zpowers wq
    have hwq2 : wq ^ 2 = 1 := by
      rw [hwq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hH, Subgroup.mem_subgroupOf]
      simpa using hw2
    have hwq1 : wq ≠ 1 := by
      intro h
      rw [hwq, QuotientGroup.eq_one_iff, hH, Subgroup.mem_subgroupOf] at h
      exact hwn h
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← Subgroup.card_top (G := Q ⧸ H), ← hgen, Nat.card_zpowers, orderOf_eq_prime hwq2 hwq1]
  rw [← Subgroup.card_mul_index H, hHcard, hHidx]

end Dicyclic

theorem torus_supply {F : Type*} [Field F] [Fintype F] (h2 : ringChar F ≠ 2) {n : ℕ}
    (hn : n ∣ Fintype.card F - 1 ∨ n ∣ Fintype.card F + 1) :
    ∃ x : SL(2, F), orderOf x = n ∧
      (x : Matrix (Fin 2) (Fin 2) F) 0 1 = (x : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  rcases hn with hn | hn
  · exact split_torus_supply (by rwa [Nat.card_eq_fintype_card])
  · exact nonsplit_torus_supply h2 hn

section Arith

variable {q : ℕ} (hq : q.Prime)
include hq

theorem factorization_card_self : (q * ((q - 1) * (q + 1))).factorization q = 1 := by
  have h2 := hq.two_le
  rw [Nat.factorization_mul hq.ne_zero (mul_ne_zero (by omega) (by omega)),
    Finsupp.add_apply, hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd]
  intro h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · have := Nat.le_of_dvd (by omega) h
    omega
  · have : q ∣ 1 := by
      have := Nat.dvd_sub h (dvd_refl q)
      simpa using this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)

theorem factorization_card_of_ne {r : ℕ} (hr : r.Prime) (hrq : r ≠ q) :
    (q * ((q - 1) * (q + 1))).factorization r
      = (q - 1).factorization r + (q + 1).factorization r := by
  have h2 := hq.two_le
  rw [Nat.factorization_mul hq.ne_zero (mul_ne_zero (by omega) (by omega)),
    Finsupp.add_apply, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd, zero_add]
  intro h
  exact hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp h)

theorem ordProj_dvd_of_odd {r : ℕ} (hr : r.Prime) (hrq : r ≠ q) (hr2 : r ≠ 2) :
    r ^ (q * ((q - 1) * (q + 1))).factorization r ∣ q - 1 ∨
      r ^ (q * ((q - 1) * (q + 1))).factorization r ∣ q + 1 := by
  have h2 := hq.two_le
  rw [factorization_card_of_ne hq hr hrq]
  by_cases hm : r ∣ q - 1
  · by_cases hp : r ∣ q + 1
    · exfalso
      have : r ∣ 2 := by
        have := Nat.dvd_sub hp hm
        rwa [show q + 1 - (q - 1) = 2 by omega] at this
      have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp this
      exact hr2 this
    · left
      rw [Nat.factorization_eq_zero_of_not_dvd hp, add_zero]
      exact Nat.ordProj_dvd _ _
  · right
    rw [Nat.factorization_eq_zero_of_not_dvd hm, zero_add]
    exact Nat.ordProj_dvd _ _

theorem two_part (hq2 : q ≠ 2) :
    ∃ e : ℕ, 2 ≤ e ∧ (q * ((q - 1) * (q + 1))).factorization 2 = e + 1 ∧
      (2 ^ e ∣ q - 1 ∨ 2 ^ e ∣ q + 1) := by
  have h2 := hq.two_le
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  rw [factorization_card_of_ne hq Nat.prime_two (Ne.symm hq2)]
  have key : ∀ {n : ℕ}, n ≠ 0 → ∀ k, (2 ^ k ∣ n ↔ k ≤ n.factorization 2) := fun hn _ =>
    Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn
  have hm0 : q - 1 ≠ 0 := by omega
  have hp0 : q + 1 ≠ 0 := by omega
  have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
  rcases (show q % 4 = 1 ∨ q % 4 = 3 by omega) with hq4 | hq4
  ·
    have ha2 : 2 ≤ (q - 1).factorization 2 :=
      (key hm0 2).mp (by rw [h4]; exact Nat.dvd_of_mod_eq_zero (by omega))
    have hb1 : 1 ≤ (q + 1).factorization 2 :=
      (key hp0 1).mp (by rw [pow_one]; exact Nat.dvd_of_mod_eq_zero (by omega))
    have hb2 : ¬ 2 ≤ (q + 1).factorization 2 := fun h => by
      have := Nat.mod_eq_zero_of_dvd ((key hp0 2).mpr h)
      rw [h4] at this
      omega
    refine ⟨(q - 1).factorization 2, ha2, by omega, Or.inl (Nat.ordProj_dvd _ _)⟩
  ·
    have hb2 : 2 ≤ (q + 1).factorization 2 :=
      (key hp0 2).mp (by rw [h4]; exact Nat.dvd_of_mod_eq_zero (by omega))
    have ha1 : 1 ≤ (q - 1).factorization 2 :=
      (key hm0 1).mp (by rw [pow_one]; exact Nat.dvd_of_mod_eq_zero (by omega))
    have ha2 : ¬ 2 ≤ (q - 1).factorization 2 := fun h => by
      have := Nat.mod_eq_zero_of_dvd ((key hm0 2).mpr h)
      rw [h4] at this
      omega
    refine ⟨(q + 1).factorization 2, hb2, by omega, Or.inr (Nat.ordProj_dvd _ _)⟩

end Arith

end IharaSchurSL2
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_of_prime.IharaSchurSL2"

open IharaSchurSL2 in

theorem IharaSchurSL2.hasTrivialSchurMultiplier_of_odd_prime
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    Ihara.HasTrivialSchurMultiplier (SL(2, ZMod q)) := by
  classical
  haveI hqf : Fact q.Prime := ⟨hq⟩
  have hchar : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq2
  have h2F : (2 : ZMod q) ≠ 0 := Ring.two_ne_zero hchar
  have hcardF : Fintype.card (ZMod q) = q := ZMod.card q

  have hN : Nat.card (SL(2, ZMod q)) = q * ((q - 1) * (q + 1)) := by rw [card_SL2, hcardF]

  apply Ihara.hasTrivialSchurMultiplier_of_sylow
  intro r hr P

  have transport : ∀ Q : Subgroup (SL(2, ZMod q)),
      Nat.card Q = r ^ (Nat.card (SL(2, ZMod q))).factorization r →
      Ihara.HasTrivialSchurMultiplier Q → Ihara.HasTrivialSchurMultiplier P := by
    intro Q hQ hQm
    exact Ihara.HasTrivialSchurMultiplier.of_mulEquiv hQm (Sylow.equiv P (Sylow.ofCard Q hQ))
  by_cases hrq : r = q
  ·
    subst hrq
    have hcardP : Nat.card P = r := by
      rw [Sylow.card_eq_multiplicity, hN, factorization_card_self hq, pow_one]
    haveI : IsCyclic P := isCyclic_of_prime_card hcardP
    exact Ihara.hasTrivialSchurMultiplier_of_isCyclic
  by_cases hr2 : r = 2
  ·
    subst hr2
    obtain ⟨e, he2, hfact, hD⟩ := two_part hq hq2
    obtain ⟨x, hxo, hxs⟩ := torus_supply hchar (n := 2 ^ e) (by rw [hcardF]; exact hD)

    set m : ℕ := 2 ^ (e - 1) with hmdef
    have hm : 2 ^ e = 2 * m := by
      rw [hmdef, ← pow_succ']; congr 1; omega
    have hxm : orderOf (x ^ m) = 2 := by
      have h := orderOf_pow_orderOf_div (x := x) (n := 2) (by rw [hxo]; positivity)
        (by rw [hxo, hm]; exact dvd_mul_right 2 m)
      rwa [hxo, hm, Nat.mul_div_cancel_left m two_pos] at h
    have hw : wSL * x * wSL⁻¹ = x⁻¹ := wSL_conj_of_symm x hxs
    have hw2eq : (wSL : SL(2, ZMod q)) ^ 2 = x ^ m := by
      apply Subtype.ext
      rw [coe_wSL_sq]
      exact (coe_eq_neg_one_of_orderOf_eq_two h2F _ hxm).symm
    have hw2 : (wSL : SL(2, ZMod q)) ^ 2 ∈ Subgroup.zpowers x :=
      hw2eq ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers x) m
    have hwn : (wSL : SL(2, ZMod q)) ∉ Subgroup.zpowers x := by
      intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hcomm : wSL * x = x * wSL := by
        rw [← hk]; exact (Commute.refl x).zpow_left k |>.eq
      have hinv : x⁻¹ = x := by rw [← hw, hcomm, mul_inv_cancel_right]
      have hx2 : x ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 1 [← hinv]
        exact inv_mul_cancel x
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
      rw [hxo] at hdvd
      have hle : 2 ^ e ≤ 2 := Nat.le_of_dvd two_pos hdvd
      have hge : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right two_pos he2
      omega

    have hxQ : x ∈ Subgroup.closure ({x, wSL} : Set (SL(2, ZMod q))) :=
      Subgroup.subset_closure (by simp)
    have hwQ : (wSL : SL(2, ZMod q)) ∈ Subgroup.closure ({x, wSL} : Set (SL(2, ZMod q))) :=
      Subgroup.subset_closure (by simp)
    have hQcard : Nat.card (Subgroup.closure ({x, wSL} : Set (SL(2, ZMod q))))
        = 2 ^ (Nat.card (SL(2, ZMod q))).factorization 2 := by
      rw [card_closure_pair_of_conj_inv hw hw2 hwn, hxo, hN, hfact, pow_succ]
    apply transport _ hQcard

    refine Ihara.hasTrivialSchurMultiplier_of_dicyclic
      (⟨x, hxQ⟩ : Subgroup.closure ({x, wSL} : Set (SL(2, ZMod q)))) ⟨wSL, hwQ⟩ m ?_ ?_ ?_ ?_
    · rw [Subgroup.orderOf_mk, hxo, hm]
    · exact Subtype.ext hw2eq
    · exact Subtype.ext hw
    · have hset : ({⟨x, hxQ⟩, ⟨wSL, hwQ⟩} : Set (Subgroup.closure ({x, wSL} : Set (SL(2, ZMod q)))))
          = ((↑) : Subgroup.closure ({x, wSL} : Set (SL(2, ZMod q))) → SL(2, ZMod q)) ⁻¹'
              {x, wSL} := by
        ext ⟨g, hg⟩
        simp [Subtype.ext_iff]
      rw [hset, Subgroup.closure_closure_coe_preimage]
  ·
    have hD := ordProj_dvd_of_odd hq hr.out hrq hr2
    obtain ⟨x, hxo, -⟩ := torus_supply hchar
      (n := r ^ (q * ((q - 1) * (q + 1))).factorization r) (by rw [hcardF]; exact hD)
    apply transport (Subgroup.zpowers x) (by rw [Nat.card_zpowers, hxo, hN])
    exact Ihara.hasTrivialSchurMultiplier_of_isCyclic

open IharaSchurSL2 in

theorem IharaSchurSL2.hasTrivialSchurMultiplier_two :
    Ihara.HasTrivialSchurMultiplier (SL(2, ZMod 2)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : Nat.card (SL(2, ZMod 2)) = 6 := by rw [card_SL2, ZMod.card]
  apply Ihara.hasTrivialSchurMultiplier_of_sylow
  intro r hr P
  have hdvd : Nat.card P ∣ 6 := hN ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup (SL(2, ZMod 2)))
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hsq : Squarefree 6 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.squarefree_mul (by norm_num)]
    exact ⟨Nat.prime_two.prime.squarefree, Nat.prime_three.prime.squarefree⟩
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have h2 : r * r ∣ 6 := by
      refine dvd_trans ?_ (hk ▸ hdvd)
      rw [← pow_two]
      exact pow_dvd_pow r (by omega)
    have := hsq r h2
    rw [Nat.isUnit_iff] at this
    exact hr.out.one_lt.ne' this
  interval_cases k
  · rw [pow_zero] at hk
    haveI : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hk).1
    exact Ihara.hasTrivialSchurMultiplier_of_subsingleton
  · rw [pow_one] at hk
    haveI : IsCyclic P := isCyclic_of_prime_card hk
    exact Ihara.hasTrivialSchurMultiplier_of_isCyclic

theorem solution
    {q : ℕ} (hq : q.Prime) :
    Ihara.HasTrivialSchurMultiplier (SL(2, ZMod q)) := by
  by_cases hq2 : q = 2
  · subst hq2
    exact IharaSchurSL2.hasTrivialSchurMultiplier_two
  · exact IharaSchurSL2.hasTrivialSchurMultiplier_of_odd_prime hq hq2

end S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_of_prime
end P2MW
export P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_of_prime (solution)
