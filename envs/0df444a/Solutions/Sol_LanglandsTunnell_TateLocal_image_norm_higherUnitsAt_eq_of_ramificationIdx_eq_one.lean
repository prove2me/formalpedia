-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/033226cc-8a18-5490-8350-3deb48f71504

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one.LanglandsTunnell.TateLocal IsDedekindDomain.HeightOneSpectrum"
open scoped nonZeroDivisors

open Filter Topology

namespace Ws45
namespace C1pRes

variable (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
  (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))

theorem coe_algebraMap_integers (x : v.adicCompletionIntegers E) :
    ((algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) x : w.1.adicCompletionIntegers M) :
        w.1.adicCompletion M) =
      algebraMap (v.adicCompletion E) (w.1.adicCompletion M) (x : v.adicCompletion E) :=
  Extension.integer_algebraMap_apply E M v w x

theorem valued_algebraMap (x : v.adicCompletion E) :
    Valued.v (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) x) =
      Valued.v x ^ v.asIdeal.ramificationIdx' w.1.asIdeal := by
  show Valued.v (Extension.adicCompletionSemialgHom E M w x) = _
  rw [Extension.valued_adicCompletionSemialgHom]
  have h : (w.1.under (𝓞 E)).asIdeal = v.asIdeal := by rw [w.2]
  rw [h]

theorem ramificationIdx_ne_zero' : v.asIdeal.ramificationIdx' w.1.asIdeal ≠ 0 := by
  have h : (w.1.under (𝓞 E)).asIdeal = v.asIdeal := by rw [w.2]
  rw [← h]
  exact ramificationIdx_ne_zero (𝓞 E) (𝓞 M) (algebraMap_injective_of_field_isFractionRing (𝓞 E) (𝓞 M) E M) w.1

private theorem _root_.Ws45.C1pRes.mem_maximalIdeal_iff {K : Type} [Field K] [NumberField K] (u : HeightOneSpectrum (𝓞 K))
    (y : u.adicCompletionIntegers K) :
    y ∈ IsLocalRing.maximalIdeal (u.adicCompletionIntegers K) ↔ Valued.v (y : u.adicCompletion K) < 1 :=
  Valuation.mem_maximalIdeal_iff (u.adicCompletion K) Valued.v

p2m_export "Ws45.C1pRes" "mem_maximalIdeal_iff"
theorem le_exp_neg_one_of_lt_one {t : WithZero (Multiplicative ℤ)} (ht : t < 1) : t ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne t 0 with rfl | h0
  · exact zero_le'
  · obtain ⟨z, rfl⟩ : ∃ z : ℤ, t = WithZero.exp z := ⟨WithZero.log t, (WithZero.exp_log h0).symm⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at ht
    rw [WithZero.exp_le_exp]
    omega

theorem map_maximalIdeal_le :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E)).map
        (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M)) ≤
      IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_maximalIdeal_iff, coe_algebraMap_integers, valued_algebraMap]
  rw [mem_maximalIdeal_iff] at hx
  exact pow_lt_one' hx (ramificationIdx_ne_zero' E M v w)

theorem map_maximalIdeal_eq (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E)).map
        (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M)) =
      IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers M) := by
  refine le_antisymm (map_maximalIdeal_le E M v w) fun y hy => ?_
  rw [mem_maximalIdeal_iff] at hy
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer E
  have hπv : Valued.v (π : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    rw [valuedAdicCompletion_eq_valuation', hπ]
  have hπint : (π : v.adicCompletion E) ∈ v.adicCompletionIntegers E := by
    rw [mem_adicCompletionIntegers, hπv, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  set πv : v.adicCompletionIntegers E := ⟨(π : v.adicCompletion E), hπint⟩ with hπvdef
  have hπmax : πv ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers E) := by
    rw [mem_maximalIdeal_iff]
    show Valued.v (π : v.adicCompletion E) < 1
    rw [hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

  have hιπ : Valued.v (algebraMap (v.adicCompletion E) (w.1.adicCompletion M) (π : v.adicCompletion E)) =
      WithZero.exp (-1 : ℤ) := by rw [valued_algebraMap, he, pow_one, hπv]
  have hι0 : algebraMap (v.adicCompletion E) (w.1.adicCompletion M) (π : v.adicCompletion E) ≠ 0 := by
    intro h; rw [h, map_zero] at hιπ; exact WithZero.coe_ne_zero hιπ.symm
  have hz : Valued.v ((y : w.1.adicCompletion M) / algebraMap (v.adicCompletion E) (w.1.adicCompletion M) (π : v.adicCompletion E)) ≤ 1 := by
    rw [map_div₀, hιπ, div_le_iff₀ (by rw [← hιπ]; exact (Valuation.pos_iff _).2 hι0), one_mul]
    exact le_exp_neg_one_of_lt_one hy
  set z : w.1.adicCompletionIntegers M :=
    ⟨(y : w.1.adicCompletion M) / algebraMap (v.adicCompletion E) (w.1.adicCompletion M) (π : v.adicCompletion E),
      (mem_adicCompletionIntegers _ _ _).2 hz⟩ with hzdef
  have hyz : y = algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) πv * z := by
    apply Subtype.ext
    show (y : w.1.adicCompletion M) = ((algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M) πv :
        w.1.adicCompletionIntegers M) : w.1.adicCompletion M) * ((y : w.1.adicCompletion M) / algebraMap (v.adicCompletion E) (w.1.adicCompletion M) (π : v.adicCompletion E))
    rw [coe_algebraMap_integers]
    show (y : w.1.adicCompletion M) = algebraMap (v.adicCompletion E) (w.1.adicCompletion M) (π : v.adicCompletion E) * _
    rw [mul_div_cancel₀ _ hι0]
  rw [hyz]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπmax)

theorem isMaximal_map_maximalIdeal (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) :
    ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers E)).map
        (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M))).IsMaximal := by
  rw [map_maximalIdeal_eq E M v w he]
  exact IsLocalRing.maximalIdeal.isMaximal _

theorem finite_residueField (K : Type) [Field K] [NumberField K] (u : HeightOneSpectrum (𝓞 K)) :
    Finite (IsLocalRing.ResidueField (u.adicCompletionIntegers K)) := by
  haveI : u.asIdeal.IsMaximal := u.isMaximal
  exact IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers K u

theorem finite_quotient_map_maximalIdeal (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) :
    Finite (w.1.adicCompletionIntegers M ⧸ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E)).map
        (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M))) := by
  haveI := finite_residueField M w.1
  exact Finite.of_equiv (IsLocalRing.ResidueField (w.1.adicCompletionIntegers M))
    (Ideal.quotEquivOfEq (map_maximalIdeal_eq E M v w he).symm).toEquiv

theorem module_finite_quotient :
    Module.Finite ((v.adicCompletionIntegers E) ⧸ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E)))
      ((w.1.adicCompletionIntegers M) ⧸ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E)).map
        (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M))) :=
  inferInstance

theorem finite_residue_base :
    Finite ((v.adicCompletionIntegers E) ⧸ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E))) :=
  finite_residueField E v

theorem isSeparable_quotient (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) :
    Algebra.IsSeparable ((v.adicCompletionIntegers E) ⧸ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E)))
      ((w.1.adicCompletionIntegers M) ⧸ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E)).map
        (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M))) := by
  haveI := isMaximal_map_maximalIdeal E M v w he
  letI := Ideal.Quotient.field ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers E)).map
        (algebraMap (v.adicCompletionIntegers E) (w.1.adicCompletionIntegers M)))
  letI : Field ((v.adicCompletionIntegers E) ⧸ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E))) :=
    Ideal.Quotient.field _
  haveI := finite_residue_base E v
  haveI := Fintype.ofFinite ((v.adicCompletionIntegers E) ⧸ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E)))
  haveI := module_finite_quotient E M v w
  haveI : PerfectField ((v.adicCompletionIntegers E) ⧸ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers E))) :=
    inferInstance
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

end Ws45.C1pRes

namespace Ws45
namespace C1pLim

p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one.LanglandsTunnell.TateLocal"

section closure
variable (K : Type) [Field K] [NumberField K] (u : HeightOneSpectrum (𝓞 K))

theorem mul_mem_higherUnitsAt {n : ℕ} {x y : (u.adicCompletion K)ˣ}
    (hx : x ∈ higherUnitsAt K u n) (hy : y ∈ higherUnitsAt K u n) : x * y ∈ higherUnitsAt K u n := by
  rw [mem_higherUnitsAt_iff] at hx hy ⊢
  refine ⟨by rw [Units.val_mul, map_mul, hx.1, hy.1, one_mul], ?_⟩
  rcases hx.2 with h0 | hxle
  · exact Or.inl h0
  rcases hy.2 with h0 | hyle
  · exact Or.inl h0
  right
  have hexp : ((x * y : (u.adicCompletion K)ˣ) : u.adicCompletion K) - 1 =
      (x : u.adicCompletion K) * ((y : u.adicCompletion K) - 1) + ((x : u.adicCompletion K) - 1) := by
    rw [Units.val_mul]; ring
  rw [hexp]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ hxle)
  rw [map_mul, hx.1, one_mul]; exact hyle

theorem inv_mem_higherUnitsAt {n : ℕ} {x : (u.adicCompletion K)ˣ}
    (hx : x ∈ higherUnitsAt K u n) : x⁻¹ ∈ higherUnitsAt K u n := by
  rw [mem_higherUnitsAt_iff] at hx ⊢
  have hinv : Valued.v ((x⁻¹ : (u.adicCompletion K)ˣ) : u.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx.1, inv_one]
  refine ⟨hinv, ?_⟩
  rcases hx.2 with h0 | hxle
  · exact Or.inl h0
  right
  have hexp : ((x⁻¹ : (u.adicCompletion K)ˣ) : u.adicCompletion K) - 1 =
      -(((x⁻¹ : (u.adicCompletion K)ˣ) : u.adicCompletion K) * ((x : u.adicCompletion K) - 1)) := by
    rw [mul_sub, mul_one, Units.inv_mul, neg_sub]
  rw [hexp, Valuation.map_neg, map_mul, hinv, one_mul]
  exact hxle

theorem prod_mem_higherUnitsAt {n : ℕ} (s : Finset ℕ) (f : ℕ → (u.adicCompletion K)ˣ)
    (hf : ∀ i ∈ s, f i ∈ higherUnitsAt K u n) : ∏ i ∈ s, f i ∈ higherUnitsAt K u n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact one_mem_higherUnitsAt K u n
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact mul_mem_higherUnitsAt K u (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem tendsto_of_valued_sub_le (x : ℕ → u.adicCompletion K) (a : u.adicCompletion K) (c : ℕ)
    (h : ∀ k, c ≤ k → Valued.v (x k - a) ≤ WithZero.exp (-(k : ℤ))) : Tendsto x atTop (𝓝 a) := by
  obtain ⟨π, hπ⟩ := u.valuation_exists_uniformizer K
  have hπv : Valued.v (π : u.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [valuedAdicCompletion_eq_valuation', hπ]
  have hπn : ‖(π : u.adicCompletion K)‖ < 1 := by
    rw [← norm_one (α := u.adicCompletion K), Valued.toNormedField.norm_lt_iff, hπv, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨c, fun k hk => ?_⟩)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπn)
  rw [norm_norm, ← norm_pow, Valued.toNormedField.norm_le_iff, map_pow, hπv, ← WithZero.exp_nsmul]
  simpa using h k hk

end closure

section cont
variable (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
  (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))

theorem continuous_norm :
    Continuous (Algebra.norm (v.adicCompletion E) : w.1.adicCompletion M → v.adicCompletion E) := by
  classical
  haveI : Module.Free (v.adicCompletion E) (w.1.adicCompletion M) := Module.Free.of_divisionRing _ _
  let b := Module.Free.chooseBasis (v.adicCompletion E) (w.1.adicCompletion M)
  have heq : (Algebra.norm (v.adicCompletion E) : w.1.adicCompletion M → v.adicCompletion E) =
      fun x => (Algebra.leftMulMatrix b x).det := funext fun x => Algebra.norm_eq_matrix_det b x
  rw [heq]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  let φ : w.1.adicCompletion M →ₗ[v.adicCompletion E] v.adicCompletion E :=
    (Matrix.entryLinearMap (v.adicCompletion E) (v.adicCompletion E) i j).comp (Algebra.leftMulMatrix b).toLinearMap
  have hφ : (fun x => Algebra.leftMulMatrix b x i j) = φ := rfl
  rw [hφ]
  exact IsModuleTopology.continuous_of_linearMap φ

end cont

section lim
variable (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
  (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M)) (m : ℕ)
  (hstep : ∀ k ≥ m, ∀ t ∈ higherUnitsAt E v k, ∃ u ∈ higherUnitsAt M w.1 k,
    t * (Units.map (Algebra.norm (v.adicCompletion E)) u)⁻¹ ∈ higherUnitsAt E v (k + 1))
  (t : (v.adicCompletion E)ˣ) (ht : t ∈ higherUnitsAt E v m)

noncomputable def T : (k : ℕ) → {s : (v.adicCompletion E)ˣ // s ∈ higherUnitsAt E v (m + k)}
  | 0 => ⟨t, by simpa using ht⟩
  | k + 1 =>
    let ih := T k
    ⟨ih.1 * (Units.map (Algebra.norm (v.adicCompletion E)) (hstep (m + k) (Nat.le_add_right m k) ih.1 ih.2).choose)⁻¹,
      (hstep (m + k) (Nat.le_add_right m k) ih.1 ih.2).choose_spec.2⟩

noncomputable def U (k : ℕ) : (w.1.adicCompletion M)ˣ :=
  (hstep (m + k) (Nat.le_add_right m k) (T E M v w m hstep t ht k).1 (T E M v w m hstep t ht k).2).choose

theorem U_mem (k : ℕ) : U E M v w m hstep t ht k ∈ higherUnitsAt M w.1 (m + k) :=
  (hstep (m + k) (Nat.le_add_right m k) (T E M v w m hstep t ht k).1 (T E M v w m hstep t ht k).2).choose_spec.1

theorem T_succ (k : ℕ) : ((T E M v w m hstep t ht (k + 1)).1 : (v.adicCompletion E)ˣ) =
    (T E M v w m hstep t ht k).1 * (Units.map (Algebra.norm (v.adicCompletion E)) (U E M v w m hstep t ht k))⁻¹ := rfl

theorem T_zero : ((T E M v w m hstep t ht 0).1 : (v.adicCompletion E)ˣ) = t := rfl

noncomputable def P (k : ℕ) : (w.1.adicCompletion M)ˣ := ∏ j ∈ Finset.range k, U E M v w m hstep t ht j

theorem P_mem (k : ℕ) : P E M v w m hstep t ht k ∈ higherUnitsAt M w.1 m :=
  prod_mem_higherUnitsAt M w.1 _ _ fun j _ => higherUnitsAt_antitone M w.1 (Nat.le_add_right m j) (U_mem E M v w m hstep t ht j)

theorem t_eq (k : ℕ) : t = Units.map (Algebra.norm (v.adicCompletion E)) (P E M v w m hstep t ht k) * (T E M v w m hstep t ht k).1 := by
  induction k with
  | zero => rw [P, Finset.range_zero, Finset.prod_empty, map_one, one_mul]; rfl
  | succ k ih =>
    rw [P, Finset.prod_range_succ, map_mul, T_succ, ← P]
    rw [mul_assoc, mul_comm (Units.map (Algebra.norm (v.adicCompletion E)) (U E M v w m hstep t ht k)) _,
      inv_mul_cancel_right]
    exact ih

theorem tendsto_P : ∃ L : w.1.adicCompletion M, Tendsto (fun k => ((P E M v w m hstep t ht k : (w.1.adicCompletion M)ˣ) : w.1.adicCompletion M)) atTop (𝓝 L) := by
  refine cauchySeq_tendsto_of_complete (NonarchimedeanAddGroup.cauchySeq_of_tendsto_sub_nhds_zero ?_)
  refine tendsto_of_valued_sub_le M w.1 _ 0 1 fun k hk => ?_
  rw [sub_zero]
  have hPk := (mem_higherUnitsAt_iff M w.1).1 (P_mem E M v w m hstep t ht k)
  have hUk := (mem_higherUnitsAt_iff M w.1).1 (U_mem E M v w m hstep t ht k)
  have hexp : ((P E M v w m hstep t ht (k + 1) : (w.1.adicCompletion M)ˣ) : w.1.adicCompletion M) - (P E M v w m hstep t ht k : (w.1.adicCompletion M)ˣ)
      = (P E M v w m hstep t ht k : (w.1.adicCompletion M)ˣ) * (((U E M v w m hstep t ht k : (w.1.adicCompletion M)ˣ) : w.1.adicCompletion M) - 1) := by
    rw [P, Finset.prod_range_succ, ← P, Units.val_mul]; ring
  rw [hexp, map_mul, hPk.1, one_mul]
  rcases hUk.2 with h0 | hle
  · omega
  · exact hle.trans (WithZero.exp_le_exp.2 (by omega))

include hstep ht in

theorem surj_of_successive : ∃ u ∈ higherUnitsAt M w.1 m, Units.map (Algebra.norm (v.adicCompletion E)) u = t := by
  obtain ⟨L, hL⟩ := tendsto_P E M v w m hstep t ht

  have hPmem : ∀ k, P E M v w m hstep t ht k ∈ higherUnitsAt M w.1 m := P_mem E M v w m hstep t ht
  have hL1 : Valued.v L = 1 := by
    have hclosed : IsClosed {x : w.1.adicCompletion M | Valued.v x = 1} := by
      have := Valued.isClosed_sphere (w.1.adicCompletion M) (Valued.v.restrict (1 : w.1.adicCompletion M))
      convert this using 2 with x
      simp
    exact hclosed.mem_of_tendsto hL (Filter.Eventually.of_forall fun k => ((mem_higherUnitsAt_iff M w.1).1 (hPmem k)).1)
  have hL0 : L ≠ 0 := by intro h; rw [h, map_zero] at hL1; exact zero_ne_one hL1
  have hLm : m = 0 ∨ Valued.v (L - 1) ≤ WithZero.exp (-(m : ℤ)) := by
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · exact Or.inl h0
    right

    obtain ⟨π, hπ⟩ := w.1.valuation_exists_uniformizer M
    have hπv : Valued.v ((π ^ m : M) : w.1.adicCompletion M) = WithZero.exp (-(m : ℤ)) := by
      rw [valuedAdicCompletion_eq_valuation', map_pow, hπ, ← WithZero.exp_nsmul]
      simp
    have hclosed : IsClosed {x : w.1.adicCompletion M | Valued.v (x - 1) ≤ WithZero.exp (-(m : ℤ))} := by
      have hc := Valued.isClosed_closedBall (w.1.adicCompletion M) (Valued.v.restrict (((π ^ m : M)) : w.1.adicCompletion M))
      have hc' : IsClosed ((fun x : w.1.adicCompletion M => x - 1) ⁻¹' {x | Valued.v.restrict x ≤ Valued.v.restrict (((π ^ m : M)) : w.1.adicCompletion M)}) :=
        hc.preimage (continuous_sub_right 1)
      have hset : {x : w.1.adicCompletion M | Valued.v (x - 1) ≤ WithZero.exp (-(m : ℤ))} =
          ((fun x : w.1.adicCompletion M => x - 1) ⁻¹' {x | Valued.v.restrict x ≤ Valued.v.restrict (((π ^ m : M)) : w.1.adicCompletion M)}) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        rw [Valuation.restrict_le_iff, hπv]
      rw [hset]
      exact hc'
    refine hclosed.mem_of_tendsto hL (Filter.Eventually.of_forall fun k => ?_)
    rcases ((mem_higherUnitsAt_iff M w.1).1 (hPmem k)).2 with h0 | hle
    · omega
    · exact hle
  refine ⟨Units.mk0 L hL0, (mem_higherUnitsAt_iff M w.1).2 ⟨hL1, hLm⟩, ?_⟩

  apply Units.ext
  have h1 : Tendsto (fun k => Algebra.norm (v.adicCompletion E) ((P E M v w m hstep t ht k : (w.1.adicCompletion M)ˣ) : w.1.adicCompletion M))
      atTop (𝓝 (Algebra.norm (v.adicCompletion E) L)) :=
    ((continuous_norm E M v w).tendsto L).comp hL
  have hT : Tendsto (fun k => (((T E M v w m hstep t ht k).1 : (v.adicCompletion E)ˣ) : v.adicCompletion E)) atTop (𝓝 1) := by
    refine tendsto_of_valued_sub_le E v _ 1 1 fun k hk => ?_
    rcases ((mem_higherUnitsAt_iff E v).1 (T E M v w m hstep t ht k).2).2 with h0 | hle
    · omega
    · exact hle.trans (WithZero.exp_le_exp.2 (by omega))
  have hTinv : Tendsto (fun k => ((((T E M v w m hstep t ht k).1 : (v.adicCompletion E)ˣ)⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E)) atTop (𝓝 1) := by
    have := (hT.inv₀ one_ne_zero)
    rw [inv_one] at this
    refine this.congr fun k => ?_
    rw [Units.val_inv_eq_inv_val]
  have h2 : Tendsto (fun k => Algebra.norm (v.adicCompletion E) ((P E M v w m hstep t ht k : (w.1.adicCompletion M)ˣ) : w.1.adicCompletion M))
      atTop (𝓝 (t : v.adicCompletion E)) := by
    have h3 : (fun k => Algebra.norm (v.adicCompletion E) ((P E M v w m hstep t ht k : (w.1.adicCompletion M)ˣ) : w.1.adicCompletion M))
        = fun k => (t : v.adicCompletion E) * ((((T E M v w m hstep t ht k).1 : (v.adicCompletion E)ˣ)⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
      funext k
      have := congrArg (fun x : (v.adicCompletion E)ˣ => (x : v.adicCompletion E)) (t_eq E M v w m hstep t ht k)
      simp only [Units.val_mul] at this
      rw [this, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      rfl
    rw [h3]
    simpa using hTinv.const_mul (t : v.adicCompletion E)
  have := tendsto_nhds_unique h1 h2
  simpa [Units.coe_map] using this

end lim

end Ws45.C1pLim

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.higherUnitsAt"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "higherUnitsAt mem_higherUnitsAt_iff mem_higherUnitsAt_zero_iff one_mem_higherUnitsAt higherUnitsAt_antitone"
namespace C1pDev
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
  (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))

set_option quotPrecheck false
local notation "𝒪v" => v.adicCompletionIntegers E
local notation "𝒪w" => (Subtype.val w).adicCompletionIntegers M
local notation "Ev" => v.adicCompletion E
local notation "Mw" => (Subtype.val w).adicCompletion M

theorem valued_algebraMap_uniformizer (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) :
    Valued.v (algebraMap (v.adicCompletion E) ((Subtype.val w).adicCompletion M)
      ((NumberField.AdelicLevel.uniformizerUnit E v : (v.adicCompletion E)ˣ) : v.adicCompletion E)) = WithZero.exp (-1 : ℤ) := by
  have h := w.valued_adicCompletionSemialgHom E M ((NumberField.AdelicLevel.uniformizerUnit E v : (v.adicCompletion E)ˣ) : v.adicCompletion E)
  have he' : (w.1.under (𝓞 E)).asIdeal.ramificationIdx' w.1.asIdeal = 1 := by
    have := w.2
    rw [this]; exact he
  rw [he', pow_one, NumberField.AdelicLevel.valued_uniformizerUnit] at h
  exact h

theorem exists_eq_uniformizer_pow_mul (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (m : ℕ) (y : (Subtype.val w).adicCompletion M)
    (hy : Valued.v y ≤ WithZero.exp (-(m : ℤ))) :
    ∃ z : (Subtype.val w).adicCompletion M, Valued.v z ≤ 1 ∧
      y = (algebraMap (v.adicCompletion E) ((Subtype.val w).adicCompletion M)
        ((NumberField.AdelicLevel.uniformizerUnit E v : (v.adicCompletion E)ˣ) : v.adicCompletion E)) ^ m * z := by
  set π := algebraMap (v.adicCompletion E) ((Subtype.val w).adicCompletion M)
        ((NumberField.AdelicLevel.uniformizerUnit E v : (v.adicCompletion E)ˣ) : v.adicCompletion E) with hπ
  have hvπ : Valued.v π = WithZero.exp (-1 : ℤ) := valued_algebraMap_uniformizer E M v w he
  have hπ0 : π ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvπ; exact WithZero.zero_ne_coe hvπ
  refine ⟨(π ^ m)⁻¹ * y, ?_, ?_⟩
  · rw [map_mul, map_inv₀, map_pow, hvπ, ← WithZero.exp_nsmul, ← WithZero.exp_neg]
    rw [show -(m • (-1 : ℤ)) = (m : ℤ) by simp]
    calc WithZero.exp (m : ℤ) * Valued.v y ≤ WithZero.exp (m : ℤ) * WithZero.exp (-(m : ℤ)) := by gcongr
      _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  · rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hπ0), one_mul]

theorem det_one_add_smul_sub_one_mem {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (c : R) (A : Matrix n n R) :
    (1 + c • A).det - 1 ∈ Ideal.span ({c} : Set R) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
  have h : (Ideal.Quotient.mk (Ideal.span ({c} : Set R))).mapMatrix (1 + c • A) = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c), zero_mul, add_zero]
    split_ifs <;> simp
  rw [RingHom.map_det, h, Matrix.det_one]

theorem norm_one_add_smul_sub_one_mem {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
    (c : R) (z : S) : Algebra.norm R (1 + c • z) - 1 ∈ Ideal.span ({c} : Set R) := by
  classical
  let b := Module.Free.chooseBasis R S
  rw [Algebra.norm_eq_matrix_det b]
  have : Algebra.leftMulMatrix b (1 + c • z) = 1 + c • Algebra.leftMulMatrix b z := by
    rw [map_add, map_one, map_smul]
  rw [this]
  exact det_one_add_smul_sub_one_mem c _

scoped instance instIsScalarTower_int : IsScalarTower (𝒪v) (𝒪w) (Mw) := .of_algebraMap_smul fun _ _ ↦ rfl

scoped instance instIsScalarTower_int' : IsScalarTower (𝒪v) (Ev) (Mw) := .of_algebraMap_smul fun _ _ ↦ rfl

theorem algebraMap_int_injective : Function.Injective (algebraMap (𝒪v) (𝒪w)) := by
  intro x y h
  have : (algebraMap (𝒪v) (Mw) x) = algebraMap (𝒪v) (Mw) y := by
    rw [IsScalarTower.algebraMap_apply (𝒪v) (𝒪w) (Mw), h, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply (𝒪v) (Ev) (Mw), IsScalarTower.algebraMap_apply (𝒪v) (Ev) (Mw)] at this
  exact Subtype.val_injective ((algebraMap (Ev) (Mw)).injective this)

scoped instance instIsTorsionFree_int : Module.IsTorsionFree (𝒪v) (𝒪w) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  exact algebraMap_int_injective E M v w

noncomputable scoped instance instFree_int : Module.Free (𝒪v) (𝒪w) := Module.free_of_finite_type_torsion_free'

theorem exists_pow_mul_mem_integers (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (y : Mw) :
    ∃ k : ℕ, Valued.v ((algebraMap (Ev) (Mw) ((NumberField.AdelicLevel.uniformizerUnit E v : (Ev)ˣ) : Ev)) ^ k * y) ≤ 1 := by
  set π := algebraMap (Ev) (Mw) ((NumberField.AdelicLevel.uniformizerUnit E v : (Ev)ˣ) : Ev) with hπ
  have hvπ : Valued.v π = WithZero.exp (-1 : ℤ) := valued_algebraMap_uniformizer E M v w he
  by_cases hy : Valued.v y = 0
  · exact ⟨0, by simp [hy]⟩
  · obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v y = WithZero.exp n := ⟨_, (WithZero.coe_unzero hy).symm⟩
    refine ⟨n.toNat, ?_⟩
    rw [map_mul, map_pow, hvπ, hn, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    rw [show n.toNat • (-1 : ℤ) + n = n - (n.toNat : ℤ) by simp [sub_eq_neg_add]]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    have := Int.self_le_toNat n
    omega

theorem instIsLocalization_int (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) :
    IsLocalization (Algebra.algebraMapSubmonoid (𝒪w) (nonZeroDivisors (𝒪v))) (Mw) where
  map_units := by
    rintro ⟨s, hs⟩
    obtain ⟨r, hr, rfl⟩ := hs
    apply IsUnit.mk0
    intro h0
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    apply hr0
    apply algebraMap_int_injective E M v w
    rw [map_zero]
    have : (algebraMap (𝒪w) (Mw) (algebraMap (𝒪v) (𝒪w) r)) = 0 := h0
    exact Subtype.val_injective (by simpa using this)
  surj := by
    intro y
    obtain ⟨k, hk⟩ := exists_pow_mul_mem_integers E M v w he y
    set πE : 𝒪v := ⟨((NumberField.AdelicLevel.uniformizerUnit E v : (Ev)ˣ) : Ev), by
      rw [mem_adicCompletionIntegers, NumberField.AdelicLevel.valued_uniformizerUnit]; exact le_of_lt (WithZero.exp_lt_exp.mpr (by norm_num))⟩ with hπE
    have hπE0 : πE ^ k ∈ nonZeroDivisors (𝒪v) := by
      apply pow_mem
      apply mem_nonZeroDivisors_of_ne_zero
      intro h0
      have := congrArg Subtype.val h0
      simp only [hπE, ZeroMemClass.coe_zero] at this
      exact (NumberField.AdelicLevel.uniformizerUnit E v).ne_zero this
    refine ⟨⟨⟨_, hk⟩, ⟨algebraMap (𝒪v) (𝒪w) (πE ^ k), _, hπE0, rfl⟩⟩, ?_⟩
    show y * (algebraMap (𝒪w) (Mw) (algebraMap (𝒪v) (𝒪w) (πE ^ k))) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝒪v) (Ev) (Mw), map_pow, map_pow, mul_comm]
    rfl
  exists_of_eq := by
    intro x y h
    exact ⟨1, by simpa using Subtype.val_injective h⟩

theorem norm_algebraMap_int (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (x : 𝒪w) :
    Algebra.norm (Ev) ((x : Mw)) = algebraMap (𝒪v) (Ev) (Algebra.norm (𝒪v) x) := by
  haveI := instIsLocalization_int E M v w he
  exact Algebra.norm_localization (𝒪v) (nonZeroDivisors (𝒪v)) (Sₘ := Mw) x

private theorem _root_.Ws45.C1pRes.norm_quotient_mk {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    [Module.Free R S] [Module.Finite R S] (x : S) :
    Algebra.norm (R ⧸ IsLocalRing.maximalIdeal R)
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) x) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (Algebra.norm R x) := by
  classical
  let ι := Module.Free.ChooseBasisIndex R S
  let b : Module.Basis ι R S := Module.Free.chooseBasis R S
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (IsLocalRing.basisQuotient b), RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.toMatrix_apply,
    IsLocalRing.basisQuotient_apply, LinearMap.mul_apply', Matrix.map_apply, ← map_mul,
    IsLocalRing.basisQuotient_repr, RingHom.mapMatrix_apply]

p2m_alias "P2MW.S_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one.Ws45.C1pRes.norm_quotient_mk" "Ws45.C1pRes.norm_quotient_mk"

theorem valued_norm_sub_one_le (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (m : ℕ) (u : (Mw)ˣ)
    (hu1 : Valued.v (u : Mw) = 1)
    (hum : Valued.v ((u : Mw) - 1) ≤ WithZero.exp (-(m : ℤ))) :
    Valued.v (((Units.map (Algebra.norm (Ev)) u : (Ev)ˣ) : Ev) - 1) ≤ WithZero.exp (-(m : ℤ)) := by
  obtain ⟨z, hz1, hyz⟩ := exists_eq_uniformizer_pow_mul E M v w he m ((u : Mw) - 1) hum
  set πE : 𝒪v := ⟨((NumberField.AdelicLevel.uniformizerUnit E v : (Ev)ˣ) : Ev), by
      rw [mem_adicCompletionIntegers, NumberField.AdelicLevel.valued_uniformizerUnit]; exact le_of_lt (WithZero.exp_lt_exp.mpr (by norm_num))⟩ with hπE
  set uI : 𝒪w := ⟨(u : Mw), by rw [mem_adicCompletionIntegers, hu1]⟩ with huI
  set zI : 𝒪w := ⟨z, (mem_adicCompletionIntegers _ _ _).mpr hz1⟩ with hzI
  have hrel : uI = 1 + (πE ^ m) • zI := by
    apply Subtype.ext
    show (u : Mw) = (1 : Mw) + ((algebraMap (𝒪v) (𝒪w) (πE ^ m)) * zI : 𝒪w)
    have hyz' : (u : Mw) = 1 + (algebraMap (Ev) (Mw) ((NumberField.AdelicLevel.uniformizerUnit E v : (Ev)ˣ) : Ev)) ^ m * z := by
      rw [← hyz]; ring
    rw [hyz']
    congr 1
    show _ = ((algebraMap (𝒪v) (𝒪w) (πE ^ m)) : Mw) * z
    congr 1
    have h1 : (((algebraMap (𝒪v) (𝒪w) (πE ^ m)) : 𝒪w) : Mw) = algebraMap (𝒪v) (Mw) (πE ^ m) :=
      (IsScalarTower.algebraMap_apply (𝒪v) (𝒪w) (Mw) (πE ^ m)).symm
    rw [h1, IsScalarTower.algebraMap_apply (𝒪v) (Ev) (Mw), map_pow, map_pow]
    rfl
  have hmem := norm_one_add_smul_sub_one_mem (πE ^ m) zI
  rw [← hrel] at hmem
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
  have hN : (((Units.map (Algebra.norm (Ev)) u : (Ev)ˣ) : Ev)) = algebraMap (𝒪v) (Ev) (Algebra.norm (𝒪v) uI) := by
    show Algebra.norm (Ev) (u : Mw) = _
    exact norm_algebraMap_int E M v w he uI
  rw [hN, show algebraMap (𝒪v) (Ev) (Algebra.norm (𝒪v) uI) - 1 = algebraMap (𝒪v) (Ev) (Algebra.norm (𝒪v) uI - 1) by rw [map_sub, map_one],
    ← ht, map_mul, map_pow]
  show Valued.v ((t : Ev) * (((NumberField.AdelicLevel.uniformizerUnit E v : (Ev)ˣ) : Ev)) ^ m) ≤ _
  rw [map_mul, map_pow, NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_nsmul,
    show m • (-1 : ℤ) = -(m : ℤ) by simp]
  calc Valued.v (t : Ev) * WithZero.exp (-(m : ℤ)) ≤ 1 * WithZero.exp (-(m : ℤ)) := by
        gcongr; exact t.2
    _ = WithZero.exp (-(m : ℤ)) := one_mul _

theorem valued_norm_eq_one (u : (Mw)ˣ) (hu : Valued.v (u : Mw) = 1) :
    Valued.v ((Units.map (Algebra.norm (Ev)) u : (Ev)ˣ) : Ev) = 1 := by
  show Valued.v (Algebra.norm (v.adicCompletion E) (u : Mw)) = 1
  rw [M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg E M v w, hu, one_pow]

theorem exists_norm_mul_mem_higherUnitsAt_one (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (t : (v.adicCompletion E)ˣ)
    (ht : t ∈ higherUnitsAt E v 0) :
    ∃ u ∈ higherUnitsAt M w.1 0, t * (Units.map (Algebra.norm (v.adicCompletion E)) u)⁻¹ ∈ higherUnitsAt E v 1 := by
  classical

  haveI := Ws45.C1pRes.isMaximal_map_maximalIdeal E M v w he
  letI := Ideal.Quotient.field ((IsLocalRing.maximalIdeal (𝒪v)).map (algebraMap (𝒪v) (𝒪w)))
  letI : Field ((𝒪v) ⧸ IsLocalRing.maximalIdeal (𝒪v)) := Ideal.Quotient.field _
  haveI : Finite ((𝒪w) ⧸ (IsLocalRing.maximalIdeal (𝒪v)).map (algebraMap (𝒪v) (𝒪w))) :=
    Ws45.C1pRes.finite_quotient_map_maximalIdeal E M v w he
  have ht1 : Valued.v (t : Ev) = 1 := (mem_higherUnitsAt_zero_iff E v).1 ht
  set tO : 𝒪v := ⟨(t : Ev), (mem_adicCompletionIntegers _ _ _).2 ht1.le⟩ with htO

  obtain ⟨ybar, hybar⟩ := FiniteField.norm_surjective (K := (𝒪v) ⧸ IsLocalRing.maximalIdeal (𝒪v))
    (K' := (𝒪w) ⧸ (IsLocalRing.maximalIdeal (𝒪v)).map (algebraMap (𝒪v) (𝒪w)))
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (𝒪v)) tO)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective ybar
  rw [Ws45.C1pRes.norm_quotient_mk, Ideal.Quotient.eq] at hybar

  have hsub : Valued.v (((Algebra.norm (𝒪v) y : 𝒪v) : Ev) - (t : Ev)) < 1 := by
    have := (Ws45.C1pRes.mem_maximalIdeal_iff v _).1 hybar
    simpa [htO] using this
  have hNy : Algebra.norm (Ev) ((y : Mw)) = ((Algebra.norm (𝒪v) y : 𝒪v) : Ev) := norm_algebraMap_int E M v w he y
  have hn1 : Valued.v ((Algebra.norm (𝒪v) y : 𝒪v) : Ev) = 1 := by
    rw [← ht1]; exact Valuation.map_eq_of_sub_lt _ (by rw [ht1]; exact hsub)
  have hn0 : ((Algebra.norm (𝒪v) y : 𝒪v) : Ev) ≠ 0 := by
    intro h; rw [h, map_zero] at hn1; exact zero_ne_one hn1

  have hunder : (w.1.under (𝓞 E)).asIdeal = v.asIdeal := by rw [w.2]
  haveI : w.1.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hunder]; rfl⟩
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hf : Ideal.inertiaDeg' v.asIdeal w.1.asIdeal ≠ 0 := Ideal.inertiaDeg_ne_zero _ _
  have hy1 : Valued.v ((y : Mw)) = 1 := by
    have h := M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg E M v w (y : Mw)
    rw [hNy, hn1] at h
    exact ((pow_eq_one_iff).1 h.symm).resolve_right hf
  have hy0 : ((y : Mw)) ≠ 0 := by intro h; rw [h, map_zero] at hy1; exact zero_ne_one hy1
  refine ⟨Units.mk0 (y : Mw) hy0, (mem_higherUnitsAt_zero_iff M w.1).2 hy1, ?_⟩
  have hcoe : ((t * (Units.map (Algebra.norm (Ev)) (Units.mk0 (y : Mw) hy0))⁻¹ : (Ev)ˣ) : Ev) =
      (t : Ev) * (((Algebra.norm (𝒪v) y : 𝒪v) : Ev))⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, Units.val_mk0, hNy]
  rw [mem_higherUnitsAt_iff, hcoe]
  refine ⟨by rw [map_mul, map_inv₀, ht1, hn1, inv_one, mul_one], Or.inr ?_⟩
  have hexp : (t : Ev) * (((Algebra.norm (𝒪v) y : 𝒪v) : Ev))⁻¹ - 1 =
      (((Algebra.norm (𝒪v) y : 𝒪v) : Ev))⁻¹ * ((t : Ev) - ((Algebra.norm (𝒪v) y : 𝒪v) : Ev)) := by
    field_simp
  rw [hexp, map_mul, map_inv₀, hn1, inv_one, one_mul, Valuation.map_sub_swap]
  simpa using Ws45.C1pRes.le_exp_neg_one_of_lt_one hsub

theorem norm_one_add_smul_sub_sub_mem {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
    (c : R) (z : S) : Algebra.norm R (1 + c • z) - 1 - c * Algebra.trace R S z ∈ Ideal.span ({c ^ 2} : Set R) := by
  classical
  let b := Module.Free.chooseBasis R S
  rw [Algebra.norm_eq_matrix_det b, Algebra.trace_eq_matrix_trace b]
  have : Algebra.leftMulMatrix b (1 + c • z) = 1 + c • Algebra.leftMulMatrix b z := by
    rw [map_add, map_one, map_smul]
  rw [this, Matrix.det_one_add_smul]
  refine Ideal.mem_span_singleton'.mpr ⟨(Matrix.det (1 + (Polynomial.X : Polynomial R) • (Algebra.leftMulMatrix b z).map Polynomial.C)).divX.divX.eval c, ?_⟩
  ring

theorem exists_trace_sub_mem_maximalIdeal (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (x : 𝒪v) :
    ∃ y : 𝒪w, Algebra.trace (𝒪v) (𝒪w) y - x ∈ IsLocalRing.maximalIdeal (𝒪v) := by
  haveI := Ws45.C1pRes.isMaximal_map_maximalIdeal E M v w he
  letI := Ideal.Quotient.field ((IsLocalRing.maximalIdeal (𝒪v)).map (algebraMap (𝒪v) (𝒪w)))
  letI : Field ((𝒪v) ⧸ IsLocalRing.maximalIdeal (𝒪v)) := Ideal.Quotient.field _
  haveI := Ws45.C1pRes.module_finite_quotient E M v w
  haveI := Ws45.C1pRes.isSeparable_quotient E M v w he
  obtain ⟨ybar, hybar⟩ := Algebra.trace_surjective ((𝒪v) ⧸ IsLocalRing.maximalIdeal (𝒪v))
    ((𝒪w) ⧸ (IsLocalRing.maximalIdeal (𝒪v)).map (algebraMap (𝒪v) (𝒪w))) (Ideal.Quotient.mk _ x)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective ybar
  refine ⟨y, ?_⟩
  rw [← Ideal.Quotient.eq, ← hybar]
  exact (Algebra.trace_quotient_mk y).symm

theorem exists_norm_mul_mem_higherUnitsAt_succ (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (m : ℕ) (hm : 1 ≤ m)
    (t : (v.adicCompletion E)ˣ) (ht : t ∈ higherUnitsAt E v m) :
    ∃ u ∈ higherUnitsAt M w.1 m, t * (Units.map (Algebra.norm (v.adicCompletion E)) u)⁻¹ ∈ higherUnitsAt E v (m + 1) := by
  classical
  obtain ⟨ht1, ht2⟩ := ht
  have htm : Valued.v ((t : Ev) - 1) ≤ WithZero.exp (-(m : ℤ)) := by
    rcases ht2 with h0 | h
    · omega
    · exact h

  set πE : 𝒪v := ⟨((NumberField.AdelicLevel.uniformizerUnit E v : (Ev)ˣ) : Ev), by
      rw [mem_adicCompletionIntegers, NumberField.AdelicLevel.valued_uniformizerUnit]
      exact le_of_lt (WithZero.exp_lt_exp.mpr (by norm_num))⟩ with hπE
  have hvπE : Valued.v (πE : Ev) = WithZero.exp (-1 : ℤ) := NumberField.AdelicLevel.valued_uniformizerUnit E v
  have hπE0 : (πE : Ev) ≠ 0 := (NumberField.AdelicLevel.uniformizerUnit E v).ne_zero
  have hvπ : Valued.v (algebraMap (Ev) (Mw) (πE : Ev)) = WithZero.exp (-1 : ℤ) :=
    valued_algebraMap_uniformizer E M v w he

  have hxv : Valued.v (((πE : Ev) ^ m)⁻¹ * ((t : Ev) - 1)) ≤ 1 := by
    rw [map_mul, map_inv₀, map_pow, hvπE, ← WithZero.exp_nsmul, ← WithZero.exp_neg,
      show -(m • (-1 : ℤ)) = (m : ℤ) by simp]
    calc WithZero.exp (m : ℤ) * Valued.v ((t : Ev) - 1) ≤ WithZero.exp (m : ℤ) * WithZero.exp (-(m : ℤ)) := by gcongr
      _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  set x : 𝒪v := ⟨_, (mem_adicCompletionIntegers _ _ _).mpr hxv⟩ with hxdef
  have hx : (t : Ev) - 1 = (πE : Ev) ^ m * (x : Ev) := by
    show (t : Ev) - 1 = (πE : Ev) ^ m * (((πE : Ev) ^ m)⁻¹ * ((t : Ev) - 1))
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hπE0), one_mul]

  obtain ⟨y, hy⟩ := exists_trace_sub_mem_maximalIdeal E M v w he x
  have hμv : Valued.v ((πE : Ev)⁻¹ * ((Algebra.trace (𝒪v) (𝒪w) y - x : 𝒪v) : Ev)) ≤ 1 := by
    have hlt := (Ws45.C1pRes.mem_maximalIdeal_iff v _).mp hy
    rw [map_mul, map_inv₀, hvπE, ← WithZero.exp_neg, neg_neg]
    calc WithZero.exp (1 : ℤ) * Valued.v ((Algebra.trace (𝒪v) (𝒪w) y - x : 𝒪v) : Ev)
        ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) := by
          gcongr; exact Ws45.C1pRes.le_exp_neg_one_of_lt_one hlt
      _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  set μ : 𝒪v := ⟨_, (mem_adicCompletionIntegers _ _ _).mpr hμv⟩ with hμdef
  have hTr : Algebra.trace (𝒪v) (𝒪w) y = x + πE * μ := by
    apply Subtype.ext
    show ((Algebra.trace (𝒪v) (𝒪w) y : 𝒪v) : Ev) = (x : Ev) + (πE : Ev) * ((πE : Ev)⁻¹ * ((Algebra.trace (𝒪v) (𝒪w) y - x : 𝒪v) : Ev))
    rw [← mul_assoc, mul_inv_cancel₀ hπE0, one_mul]
    try push_cast
    try ring

  set uI : 𝒪w := 1 + (πE ^ m) • y with huI
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp (norm_one_add_smul_sub_sub_mem (πE ^ m) y)
  have hpow : (πE ^ m) ^ 2 = πE ^ (m + 1) * πE ^ (m - 1) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have hnorm : Algebra.norm (𝒪v) uI = 1 + πE ^ m * x + πE ^ (m + 1) * (μ + πE ^ (m - 1) * q) := by
    rw [huI]
    linear_combination (-1 : 𝒪v) * hq + πE ^ m * hTr + q * hpow

  have hcoe : (uI : Mw) = 1 + (algebraMap (Ev) (Mw) (πE : Ev)) ^ m * (y : Mw) := by
    rw [huI]
    push_cast
    rw [Algebra.smul_def]
    push_cast
    congr 2
  have hu1v : Valued.v ((uI : Mw) - 1) ≤ WithZero.exp (-(m : ℤ)) := by
    rw [hcoe, add_sub_cancel_left, map_mul, map_pow, hvπ, ← WithZero.exp_nsmul,
      show m • (-1 : ℤ) = -(m : ℤ) by simp]
    calc WithZero.exp (-(m : ℤ)) * Valued.v (y : Mw) ≤ WithZero.exp (-(m : ℤ)) * 1 := by gcongr; exact y.2
      _ = WithZero.exp (-(m : ℤ)) := mul_one _
  have hexp_lt : WithZero.exp (-(m : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have huv : Valued.v (uI : Mw) = 1 := by
    rw [show (uI : Mw) = 1 + ((uI : Mw) - 1) by ring]
    exact Valuation.map_one_add_of_lt _ (lt_of_le_of_lt hu1v hexp_lt)
  have hu0 : (uI : Mw) ≠ 0 := fun h => by rw [h, map_zero] at huv; exact zero_ne_one huv
  refine ⟨Units.mk0 (uI : Mw) hu0, ⟨huv, Or.inr hu1v⟩, ?_⟩

  have hN : ((Units.map (Algebra.norm (Ev)) (Units.mk0 (uI : Mw) hu0) : (Ev)ˣ) : Ev) =
      algebraMap (𝒪v) (Ev) (Algebra.norm (𝒪v) uI) := by
    show Algebra.norm (Ev) (uI : Mw) = _
    exact norm_algebraMap_int E M v w he uI
  have hNv : Valued.v ((Units.map (Algebra.norm (Ev)) (Units.mk0 (uI : Mw) hu0) : (Ev)ˣ) : Ev) = 1 :=
    valued_norm_eq_one E M v w _ huv
  have hN0 : ((Units.map (Algebra.norm (Ev)) (Units.mk0 (uI : Mw) hu0) : (Ev)ˣ) : Ev) ≠ 0 := Units.ne_zero _
  have hdiff : (t : Ev) - ((Units.map (Algebra.norm (Ev)) (Units.mk0 (uI : Mw) hu0) : (Ev)ˣ) : Ev) =
      -((πE : Ev) ^ (m + 1) * ((μ + πE ^ (m - 1) * q : 𝒪v) : Ev)) := by
    have halg : ∀ z : 𝒪v, algebraMap (𝒪v) (Ev) z = (z : Ev) := fun _ => rfl
    rw [hN, hnorm, halg]
    have ht' : (t : Ev) = 1 + (πE : Ev) ^ m * (x : Ev) := by linear_combination hx
    rw [ht']
    push_cast
    ring

  rw [mem_higherUnitsAt_iff]
  refine ⟨?_, Or.inr ?_⟩
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, ht1, hNv, inv_one, mul_one]
  · have hrw : ((t * (Units.map (Algebra.norm (Ev)) (Units.mk0 (uI : Mw) hu0))⁻¹ : (Ev)ˣ) : Ev) - 1 =
        ((t : Ev) - ((Units.map (Algebra.norm (Ev)) (Units.mk0 (uI : Mw) hu0) : (Ev)ˣ) : Ev)) *
          (((Units.map (Algebra.norm (Ev)) (Units.mk0 (uI : Mw) hu0) : (Ev)ˣ) : Ev))⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    rw [hrw, map_mul, map_inv₀, hNv, inv_one, mul_one, hdiff, Valuation.map_neg, map_mul, map_pow, hvπE,
      ← WithZero.exp_nsmul, show (m + 1) • (-1 : ℤ) = -((m + 1 : ℕ) : ℤ) by simp]
    calc WithZero.exp (-((m + 1 : ℕ) : ℤ)) * Valued.v ((μ + πE ^ (m - 1) * q : 𝒪v) : Ev)
        ≤ WithZero.exp (-((m + 1 : ℕ) : ℤ)) * 1 := by gcongr; exact (μ + πE ^ (m - 1) * q).2
      _ = WithZero.exp (-((m + 1 : ℕ) : ℤ)) := mul_one _

private theorem _root_.LanglandsTunnell.TateLocal.C1pDev.surj_of_successive (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (m : ℕ)
    (hstep : ∀ k ≥ m, ∀ t ∈ higherUnitsAt E v k, ∃ u ∈ higherUnitsAt M w.1 k, t * (Units.map (Algebra.norm (v.adicCompletion E)) u)⁻¹ ∈ higherUnitsAt E v (k + 1))
    (t : (v.adicCompletion E)ˣ) (ht : t ∈ higherUnitsAt E v m) :
    ∃ u ∈ higherUnitsAt M w.1 m, Units.map (Algebra.norm (v.adicCompletion E)) u = t :=
  Ws45.C1pLim.surj_of_successive E M v w m hstep t ht

p2m_export "LanglandsTunnell.TateLocal.C1pDev" "surj_of_successive"

theorem image_norm_higherUnitsAt_eq (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (m : ℕ) :
    (Units.map (Algebra.norm (v.adicCompletion E))) '' higherUnitsAt M w.1 m = higherUnitsAt E v m := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_higherUnitsAt_iff] at hu ⊢
    refine ⟨valued_norm_eq_one E M v w u hu.1, ?_⟩
    rcases hu.2 with h0 | hle
    · exact Or.inl h0
    · exact Or.inr (valued_norm_sub_one_le E M v w he m u hu.1 hle)
  · intro ht
    have hstep : ∀ k ≥ m, ∀ t ∈ higherUnitsAt E v k, ∃ u ∈ higherUnitsAt M w.1 k, t * (Units.map (Algebra.norm (v.adicCompletion E)) u)⁻¹ ∈ higherUnitsAt E v (k + 1) := by
      intro k _ t ht
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact exists_norm_mul_mem_higherUnitsAt_one E M v w he t ht
      · exact exists_norm_mul_mem_higherUnitsAt_succ E M v w he k hk t ht
    obtain ⟨u, hu, hNu⟩ := surj_of_successive E M v w he m hstep t ht
    exact ⟨u, hu, hNu⟩

end LanglandsTunnell.TateLocal.C1pDev
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one.LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one.LanglandsTunnell.TateLocal.C1pDev"
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one.LanglandsTunnell.TateLocal"
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one.LanglandsTunnell"

theorem solution
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (m : ℕ) :
    (Units.map (Algebra.norm (v.adicCompletion E))) '' LanglandsTunnell.TateLocal.higherUnitsAt M w.1 m =
      LanglandsTunnell.TateLocal.higherUnitsAt E v m :=
  LanglandsTunnell.TateLocal.C1pDev.image_norm_higherUnitsAt_eq E M v w he m

end S_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one (solution)
