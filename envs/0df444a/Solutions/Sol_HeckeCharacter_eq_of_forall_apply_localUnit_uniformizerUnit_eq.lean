-- Prove2me | solution 1 for HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e2e736b1-51df-59cc-90e1-945ce4d632aa

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel AutomorphicForm
open scoped Topology

section IdeleCharacter

variable (F : Type*) [Field F] [NumberField F]

private noncomputable def ideleChar_archIncl : InfiniteAdeleRing F →* AdeleRing (𝓞 F) F where
  toFun z := (z, (1 : FiniteAdeleRing (𝓞 F) F))
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (one_mul _).symm

private theorem ideleChar_continuous_archIncl : Continuous (ideleChar_archIncl F) :=
  (continuous_id.prodMk continuous_const :
    Continuous fun z : InfiniteAdeleRing F =>
      ((z, (1 : FiniteAdeleRing (𝓞 F) F)) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

private noncomputable def ideleChar_component (v : HeightOneSpectrum (𝓞 F)) :
    (FiniteAdeleRing (𝓞 F) F)ˣ →* (v.adicCompletion F)ˣ :=
  Units.map (finAdeleEval (𝓞 F) F v)

private noncomputable def ideleChar_archInv : InfiniteAdeleRing F → InfiniteAdeleRing F :=
  fun z w => (z w)⁻¹

private noncomputable def ideleChar_ball (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) (n : ℕ) :
    Set (v.adicCompletion F) :=
  {b | Valued.v (b - a) ≤ Valued.v ((uniformizerUnit F v : v.adicCompletion F) ^ (n + 1) * a)}

variable {F}

private theorem ideleChar_fin_apply_ne_zero (u : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (u : AdeleRing (𝓞 F) F).2 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (congrArg (fun a : AdeleRing (𝓞 F) F => a.2 v) u.mul_inv)

private theorem ideleChar_idele_decomp (u : (AdeleRing (𝓞 F) F)ˣ) :
    u = Units.map (ideleChar_archIncl F) (Units.map (adeleArch (𝓞 F) F) u) *
        Units.map (finIncl (𝓞 F) F) (Units.map (adeleFin (𝓞 F) F) u) :=
  Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)

private theorem ideleChar_component_apply (v : HeightOneSpectrum (𝓞 F)) (y : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (ideleChar_component F v y : v.adicCompletion F) = (y : FiniteAdeleRing (𝓞 F) F) v := rfl

private theorem ideleChar_component_localUnit_self (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ideleChar_component F v (localUnit (𝓞 F) F v t) = t :=
  Units.ext (localUnit_apply_self (𝓞 F) F v t)

private theorem ideleChar_component_localUnit_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w)
    (t : (w.adicCompletion F)ˣ) : ideleChar_component F v (localUnit (𝓞 F) F w t) = 1 :=
  Units.ext (localUnit_apply_of_ne (𝓞 F) F w t h)

omit [NumberField F] in
private theorem ideleChar_arch_apply_ne_zero (z : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    (z : InfiniteAdeleRing F) w ≠ 0 :=
  left_ne_zero_of_mul_eq_one
    (congrFun (congrArg (fun a : InfiniteAdeleRing F => (a : (w' : InfinitePlace F) → w'.Completion))
      z.mul_inv) w)

omit [NumberField F] in
private theorem ideleChar_arch_val_inv (z : (InfiniteAdeleRing F)ˣ) :
    ((z⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = ideleChar_archInv F (z : InfiniteAdeleRing F) :=
  funext fun w => eq_inv_of_mul_eq_one_right
    (congrFun (congrArg (fun a : InfiniteAdeleRing F => (a : (w' : InfinitePlace F) → w'.Completion))
      z.mul_inv) w)

omit [NumberField F] in
private theorem ideleChar_continuousAt_archInv (p : InfiniteAdeleRing F) (hp : ∀ w, p w ≠ 0) :
    ContinuousAt (ideleChar_archInv F) p :=
  continuousAt_pi.mpr fun w => (continuousAt_inv₀ (hp w)).comp (continuousAt_apply w p)

private theorem ideleChar_valued_ne_zero {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F} (ha : a ≠ 0) :
    Valued.v a ≠ 0 :=
  (map_ne_zero (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).mpr ha

private theorem ideleChar_finite_supp {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) :
    {v : HeightOneSpectrum (𝓞 F) | HeckeCharacter.idealMultiplicity F v 𝔣 ≠ 0}.Finite :=
  (Ideal.finite_factors (show 𝔣 ≠ 0 from h𝔣)).subset fun v hv =>
    (Associates.count_ne_zero_iff_dvd (show 𝔣 ≠ 0 from h𝔣) v.irreducible).mp hv

private theorem ideleChar_ball_mem_nhds (v : HeightOneSpectrum (𝓞 F)) {a : v.adicCompletion F} (ha : a ≠ 0)
    (n : ℕ) : ideleChar_ball F v a n ∈ nhds a := by
  have ht : (uniformizerUnit F v : v.adicCompletion F) ^ (n + 1) * a ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (uniformizerUnit F v).ne_zero) ha
  have hopen : IsOpen (ideleChar_ball F v a n) :=
    (isOpen_setOf_valued_le v _ ht).preimage (continuous_id.sub continuous_const)
  refine hopen.mem_nhds ?_
  show Valued.v (a - a) ≤ _
  rw [sub_self, map_zero]
  exact zero_le'

private theorem ideleChar_congruence {v : HeightOneSpectrum (𝓞 F)} {a b : v.adicCompletion F} (ha : a ≠ 0)
    (n : ℕ) (hb : b ∈ ideleChar_ball F v a n) :
    Valued.v (a * b⁻¹) = 1 ∧ Valued.v (a * b⁻¹ - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  change Valued.v (b - a) ≤ Valued.v ((uniformizerUnit F v : v.adicCompletion F) ^ (n + 1) * a) at hb
  have ha0 : Valued.v a ≠ 0 := ideleChar_valued_ne_zero ha
  obtain ⟨m, hm⟩ : ∃ m : ℤ, WithZero.exp m = Valued.v a := ⟨_, WithZero.exp_log ha0⟩
  have ht : Valued.v ((uniformizerUnit F v : v.adicCompletion F) ^ (n + 1) * a)
      = WithZero.exp (m - (n + 1 : ℤ)) := by
    rw [map_mul, map_pow, valued_uniformizerUnit, ← hm, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    congr 1
    rw [nsmul_eq_mul]
    push_cast
    ring
  rw [ht] at hb
  have hlt : Valued.v (b - a) < Valued.v a := by
    rw [← hm]
    exact hb.trans_lt (WithZero.exp_lt_exp.mpr (by omega))
  have hba : Valued.v b = Valued.v a := Valuation.map_eq_of_sub_lt _ hlt
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, map_zero] at hba
    exact ha0 hba.symm
  refine ⟨?_, ?_⟩
  · rw [map_mul, map_inv₀, hba, mul_inv_cancel₀ ha0]
  · have h2 : a * b⁻¹ - 1 = (a - b) * b⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ hb0]
    rw [h2, map_mul, map_inv₀, hba, Valuation.map_sub_swap, ← hm]
    calc Valued.v (b - a) * (WithZero.exp m)⁻¹
        ≤ WithZero.exp (m - (n + 1 : ℤ)) * (WithZero.exp m)⁻¹ := mul_le_mul_left hb _
      _ = WithZero.exp (-(n + 1 : ℤ)) := by
          rw [← WithZero.exp_neg, ← WithZero.exp_add]
          congr 1
          ring
      _ ≤ WithZero.exp (-(n : ℤ)) := WithZero.exp_le_exp.mpr (by omega)

private theorem ideleChar_finIncl_eq_one (θ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {𝔣 : Ideal (𝓞 F)}
    (hmod : HeckeCharacter.AdmitsModulus F θ 𝔣) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ v ∉ S, θ (Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (uniformizerUnit F v))) = 1)
    (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ S ∨ HeckeCharacter.idealMultiplicity F v 𝔣 ≠ 0 →
      Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) = 1 ∧
        Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v - 1)
          ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F v 𝔣 : ℤ))) :
    θ (Units.map (finIncl (𝓞 F) F) y) = 1 := by
  obtain ⟨hne, hcof⟩ := IsDedekindDomain.FiniteAdeleRing.isUnit_iff.mp y.isUnit
  have hZ : {v : HeightOneSpectrum (𝓞 F) | Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) ≠ 1}.Finite :=
    Filter.eventually_cofinite.mp hcof
  have hv0 : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) ≠ 0 :=
    fun v => ideleChar_valued_ne_zero (hne v)
  obtain ⟨k, hk⟩ : ∃ k : HeightOneSpectrum (𝓞 F) → ℤ,
      ∀ v, WithZero.exp (k v) = Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) :=
    ⟨fun v => WithZero.log _, fun v => WithZero.exp_log (hv0 v)⟩
  have hZS : ∀ v ∈ hZ.toFinset, v ∉ S := by
    intro v hv hvS
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
    exact hv (hy v (Or.inl hvS)).1
  have hnotZ : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) = 1 →
      v ∉ hZ.toFinset := by
    intro v h1 hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
    exact hv h1

  obtain ⟨c, hc⟩ : ∃ c : (FiniteAdeleRing (𝓞 F) F)ˣ,
      c = ∏ v ∈ hZ.toFinset, localUnit (𝓞 F) F v (uniformizerUnit F v ^ (-(k v))) := ⟨_, rfl⟩
  have hθc : θ (Units.map (finIncl (𝓞 F) F) c) = 1 := by
    rw [hc, map_prod, map_prod]
    refine Finset.prod_eq_one fun v hv => ?_
    rw [map_zpow, map_zpow, map_zpow, hS v (hZS v hv), _root_.one_zpow]
  have hevc_in : ∀ v ∈ hZ.toFinset, ideleChar_component F v c = uniformizerUnit F v ^ (-(k v)) := by
    intro v hv
    rw [hc, map_prod, Finset.prod_eq_single v]
    · exact ideleChar_component_localUnit_self v _
    · intro w _ hwv
      exact ideleChar_component_localUnit_of_ne (Ne.symm hwv) _
    · intro h
      exact absurd hv h
  have hevc_out : ∀ v, v ∉ hZ.toFinset → ideleChar_component F v c = 1 := by
    intro v hv
    rw [hc, map_prod]
    refine Finset.prod_eq_one fun w hw => ?_
    refine ideleChar_component_localUnit_of_ne (fun hvw => hv ?_) _
    rw [hvw]
    exact hw

  obtain ⟨u, hu⟩ : ∃ u : (FiniteAdeleRing (𝓞 F) F)ˣ, u = y * c⁻¹ := ⟨_, rfl⟩
  have hyu : y = u * c := by
    rw [hu]
    simp
  have hu_out : ∀ v, v ∉ hZ.toFinset →
      (u : FiniteAdeleRing (𝓞 F) F) v = (y : FiniteAdeleRing (𝓞 F) F) v := by
    intro v hv
    change (ideleChar_component F v u : v.adicCompletion F) = ideleChar_component F v y
    rw [hu, map_mul, map_inv, hevc_out v hv, inv_one, mul_one]
  have hu_val : ∀ v, Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    intro v
    by_cases hv : v ∈ hZ.toFinset
    · change Valued.v (ideleChar_component F v u : v.adicCompletion F) = 1
      rw [hu, map_mul, map_inv, hevc_in v hv, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, valued_uniformizerUnit, ideleChar_component_apply,
        ← hk v, ← WithZero.exp_zsmul]
      have h1 : (-(k v)) • (-1 : ℤ) = k v := by simp
      rw [h1]
      exact mul_inv_cancel₀ WithZero.exp_ne_zero
    · rw [hu_out v hv]
      by_contra h
      exact hv (by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact h)
  have hu_cong : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v - 1)
        ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F v 𝔣 : ℤ)) := by
    intro v
    by_cases hn : HeckeCharacter.idealMultiplicity F v 𝔣 = 0
    · rw [hn, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact (Valuation.map_sub Valued.v _ _).trans (max_le (hu_val v).le (map_one Valued.v).le)
    · have hvZ : v ∉ hZ.toFinset := hnotZ v (hy v (Or.inr hn)).1
      rw [hu_out v hvZ]
      exact (hy v (Or.inr hn)).2
  have hθu : θ (Units.map (finIncl (𝓞 F) F) u) = 1 :=
    hmod (Units.map (finIncl (𝓞 F) F) u) rfl fun v => ⟨hu_val v, hu_cong v⟩
  rw [hyu, map_mul, map_mul, hθu, hθc, one_mul]

private theorem ideleChar_eq_one_of_denseRange (F : Type*) [Field F] [NumberField F]
    (hwa : ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
      DenseRange (fun x : F =>
        ((fun v : S => algebraMap F (v.1.adicCompletion F) x),
         (fun w : NumberField.InfinitePlace F => algebraMap F w.Completion x))))
    (θ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hcont : Continuous θ)
    (hclass : AutomorphicForm.IsIdeleClassChar (𝓞 F) F θ)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (hmod : HeckeCharacter.AdmitsModulus F θ 𝔣)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, θ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F)
        (NumberField.AdelicLevel.localUnit (𝓞 F) F v (NumberField.AdelicLevel.uniformizerUnit F v))) = 1) :
    θ = 1 := by
  classical
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.one_apply]

  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 F)), T = S ∪ (ideleChar_finite_supp h𝔣).toFinset :=
    ⟨_, rfl⟩
  have hmemT : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ S ∨ HeckeCharacter.idealMultiplicity F v 𝔣 ≠ 0 →
      v ∈ T := by
    intro v hv
    rw [hT, Finset.mem_union]
    rcases hv with h | h
    · exact Or.inl h
    · right
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact h

  have hx2 : ∀ v : HeightOneSpectrum (𝓞 F), (x : AdeleRing (𝓞 F) F).2 v ≠ 0 :=
    ideleChar_fin_apply_ne_zero x
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : (InfiniteAdeleRing F)ˣ, x₁ = Units.map (adeleArch (𝓞 F) F) x := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (InfiniteAdeleRing F)ˣ → ℂˣ,
      ∀ z, ψ z = θ (Units.map (ideleChar_archIncl F) (x₁ * z⁻¹)) :=
    ⟨fun z => θ (Units.map (ideleChar_archIncl F) (x₁ * z⁻¹)), fun _ => rfl⟩
  have hψ_cont : Continuous ψ := by
    have hψ' : ψ = fun z => θ (Units.map (ideleChar_archIncl F) (x₁ * z⁻¹)) := funext hψ
    rw [hψ']
    exact (hcont.comp (Continuous.units_map _ (ideleChar_continuous_archIncl F))).comp
      (continuous_const.mul continuous_inv)
  have hψ_one : ψ x₁ = 1 := by
    rw [hψ]
    simp

  have hstepA : ∀ N ∈ nhds (x₁ : InfiniteAdeleRing F),
      ∃ z : (InfiniteAdeleRing F)ˣ, (z : InfiniteAdeleRing F) ∈ N ∧ θ x = ψ z := by
    intro N hN
    obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
    obtain ⟨E, hE⟩ : ∃ E : Set (InfiniteAdeleRing F), E = archEval F w₀ ⁻¹' {c | c ≠ 0} := ⟨_, rfl⟩
    have hEN : E ∈ nhds (x₁ : InfiniteAdeleRing F) := by
      rw [hE]
      exact ((isOpen_ne (x := (0 : w₀.Completion))).preimage (continuous_archEval F w₀)).mem_nhds
        (ideleChar_arch_apply_ne_zero x₁ w₀)
    have hN' : N ∩ E ∈ nhds (x₁ : InfiniteAdeleRing F) := Filter.inter_mem hN hEN
    have hpi : Set.univ.pi (fun v : T => ideleChar_ball F v.1 ((x : AdeleRing (𝓞 F) F).2 v.1)
          (HeckeCharacter.idealMultiplicity F v.1 𝔣))
        ∈ nhds (fun v : T => (x : AdeleRing (𝓞 F) F).2 v.1) :=
      set_pi_mem_nhds Set.finite_univ fun v _ => ideleChar_ball_mem_nhds v.1 (hx2 v.1) _
    obtain ⟨pt, hpt_def⟩ : ∃ pt : ((v : T) → v.1.adicCompletion F) × InfiniteAdeleRing F,
        pt = ((fun v : T => (x : AdeleRing (𝓞 F) F).2 v.1), (x₁ : InfiniteAdeleRing F)) := ⟨_, rfl⟩
    have hU : (Set.univ.pi (fun v : T => ideleChar_ball F v.1 ((x : AdeleRing (𝓞 F) F).2 v.1)
          (HeckeCharacter.idealMultiplicity F v.1 𝔣))) ×ˢ (N ∩ E) ∈ nhds pt := by
      rw [hpt_def, nhds_prod_eq]
      exact Filter.prod_mem_prod hpi hN'
    have hpt := hwa T pt
    obtain ⟨q, hqU, α, hαq⟩ := mem_closure_iff_nhds.mp hpt _ hU
    subst hαq
    have hfin : ∀ v : T, algebraMap F (v.1.adicCompletion F) α ∈ ideleChar_ball F v.1
        ((x : AdeleRing (𝓞 F) F).2 v.1) (HeckeCharacter.idealMultiplicity F v.1 𝔣) :=
      fun v => (Set.mem_univ_pi.mp hqU.1) v
    have harch : (algebraMap F (AdeleRing (𝓞 F) F) α).1 ∈ N ∩ E := hqU.2
    have hα0 : α ≠ 0 := by
      intro h
      have h2 := harch.2
      rw [hE, Set.mem_preimage, Set.mem_setOf_eq, archEval_apply] at h2
      subst h
      exact h2 (map_zero (algebraMap F w₀.Completion))

    obtain ⟨P, hP⟩ : ∃ P : (AdeleRing (𝓞 F) F)ˣ,
        P = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) (Units.mk0 α hα0) := ⟨_, rfl⟩
    have hθP : θ P = 1 := by
      rw [hP]
      exact hclass _
    have hcomp : ∀ v : HeightOneSpectrum (𝓞 F),
        ((Units.map (adeleFin (𝓞 F) F) (x * P⁻¹) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v
          = (x : AdeleRing (𝓞 F) F).2 v * (algebraMap F (v.adicCompletion F) α)⁻¹ := by
      intro v
      rw [hP, ← map_inv₀]
      rfl
    have hyf : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ S ∨ HeckeCharacter.idealMultiplicity F v 𝔣 ≠ 0 →
        Valued.v (((Units.map (adeleFin (𝓞 F) F) (x * P⁻¹) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
            FiniteAdeleRing (𝓞 F) F) v) = 1 ∧
          Valued.v (((Units.map (adeleFin (𝓞 F) F) (x * P⁻¹) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
            FiniteAdeleRing (𝓞 F) F) v - 1)
            ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F v 𝔣 : ℤ)) := by
      intro v hv
      have hb : algebraMap F (v.adicCompletion F) α ∈ ideleChar_ball F v ((x : AdeleRing (𝓞 F) F).2 v)
          (HeckeCharacter.idealMultiplicity F v 𝔣) := hfin ⟨v, hmemT v hv⟩
      rw [hcomp v]
      exact ideleChar_congruence (hx2 v) _ hb
    have hθfin : θ (Units.map (finIncl (𝓞 F) F) (Units.map (adeleFin (𝓞 F) F) (x * P⁻¹))) = 1 :=
      ideleChar_finIncl_eq_one θ hmod hS _ hyf

    refine ⟨Units.map (adeleArch (𝓞 F) F) P, ?_, ?_⟩
    · rw [hP]
      exact harch.1
    · have h1 : θ x = θ (x * P⁻¹) := by
        rw [map_mul, map_inv, hθP, inv_one, mul_one]
      have h3 : Units.map (adeleArch (𝓞 F) F) (x * P⁻¹) = x₁ * (Units.map (adeleArch (𝓞 F) F) P)⁻¹ := by
        rw [map_mul, map_inv, hx₁]
      rw [h1, ideleChar_idele_decomp (x * P⁻¹), map_mul, hθfin, mul_one, hψ, h3]

  refine Specializes.eq ?_
  rw [specializes_iff_forall_open]
  intro V hV h1V
  have hVψ : ψ ⁻¹' V ∈ nhds x₁ :=
    hψ_cont.continuousAt.preimage_mem_nhds (by rw [hψ_one]; exact hV.mem_nhds h1V)
  rw [(Units.isEmbedding_embedProduct (M := InfiniteAdeleRing F)).toIsInducing.nhds_eq_comap x₁,
    Filter.mem_comap] at hVψ
  obtain ⟨Q, hQ, hQsub⟩ := hVψ
  change Q ∈ nhds ((x₁ : InfiniteAdeleRing F),
    MulOpposite.op ((x₁⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)) at hQ
  rw [mem_nhds_prod_iff] at hQ
  obtain ⟨A, hA, B', hB', hAB⟩ := hQ
  have hB : MulOpposite.op ⁻¹' B' ∈ nhds ((x₁⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB'
  rw [ideleChar_arch_val_inv x₁] at hB
  have hB2 : ideleChar_archInv F ⁻¹' (MulOpposite.op ⁻¹' B') ∈ nhds (x₁ : InfiniteAdeleRing F) :=
    (ideleChar_continuousAt_archInv (x₁ : InfiniteAdeleRing F) (ideleChar_arch_apply_ne_zero x₁)).preimage_mem_nhds hB
  obtain ⟨z, hz, hθz⟩ := hstepA (A ∩ ideleChar_archInv F ⁻¹' (MulOpposite.op ⁻¹' B')) (Filter.inter_mem hA hB2)
  have hz2 : MulOpposite.op ((z⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) ∈ B' := by
    rw [ideleChar_arch_val_inv z]
    exact hz.2
  have hzQ : z ∈ Units.embedProduct (InfiniteAdeleRing F) ⁻¹' Q := by
    change ((z : InfiniteAdeleRing F),
      MulOpposite.op ((z⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)) ∈ Q
    exact hAB (Set.mk_mem_prod hz.1 hz2)
  rw [hθz]
  exact hQsub hzQ

private theorem ideleChar_eq_one (F : Type*) [Field F] [NumberField F]
    (θ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hcont : Continuous θ)
    (hclass : AutomorphicForm.IsIdeleClassChar (𝓞 F) F θ)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (hmod : HeckeCharacter.AdmitsModulus F θ 𝔣)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, θ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F)
        (NumberField.AdelicLevel.localUnit (𝓞 F) F v (NumberField.AdelicLevel.uniformizerUnit F v))) = 1) :
    θ = 1 :=
  ideleChar_eq_one_of_denseRange F NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi
    θ hcont hclass 𝔣 h𝔣 hmod S hS

end IdeleCharacter

section Reduction

variable {K : Type*} [Field K] [NumberField K]

private theorem idealMultiplicity_le_of_dvd {𝔞 𝔟 : Ideal (𝓞 K)} (h𝔟 : 𝔟 ≠ ⊥) (h : 𝔞 ∣ 𝔟)
    (v : HeightOneSpectrum (𝓞 K)) :
    HeckeCharacter.idealMultiplicity K v 𝔞 ≤ HeckeCharacter.idealMultiplicity K v 𝔟 := by
  unfold HeckeCharacter.idealMultiplicity
  refine Associates.count_le_count_of_le ?_ v.associates_irreducible (Associates.mk_le_mk_of_dvd h)
  rw [Ne, Associates.mk_eq_zero, Ideal.zero_eq_bot]
  exact h𝔟

private theorem admitsModulus_of_forall_le {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {𝔞 𝔟 : Ideal (𝓞 K)}
    (hχ : HeckeCharacter.AdmitsModulus K χ 𝔞)
    (hle : ∀ v : HeightOneSpectrum (𝓞 K),
      HeckeCharacter.idealMultiplicity K v 𝔞 ≤ HeckeCharacter.idealMultiplicity K v 𝔟) :
    HeckeCharacter.AdmitsModulus K χ 𝔟 := by
  intro u h1 h2
  refine hχ u h1 (fun v => ⟨(h2 v).1, le_trans (h2 v).2 ?_⟩)
  rw [WithZero.exp_le_exp]
  exact neg_le_neg (by exact_mod_cast hle v)

private theorem idealMultiplicity_bot (v : HeightOneSpectrum (𝓞 K)) :
    HeckeCharacter.idealMultiplicity K v (⊥ : Ideal (𝓞 K)) = 0 := by
  unfold HeckeCharacter.idealMultiplicity
  rw [← Ideal.zero_eq_bot, Associates.mk_zero, Associates.factors_zero]
  by_cases hp : Irreducible (Associates.mk v.asIdeal)
  · simp only [Associates.count, dif_pos hp]
    rfl
  · exact congrFun (Associates.count_reducible hp) _

private theorem exists_ne_bot_admitsModulus {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {𝔣 : Ideal (𝓞 K)}
    (hχ : HeckeCharacter.AdmitsModulus K χ 𝔣) :
    ∃ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus K χ 𝔪 := by
  by_cases h𝔣 : 𝔣 = ⊥
  · subst h𝔣
    refine ⟨⊤, ?_, admitsModulus_of_forall_le hχ (fun v => ?_)⟩
    · exact fun h => bot_ne_top h.symm
    · rw [idealMultiplicity_bot]
      exact Nat.zero_le _
  · exact ⟨𝔣, h𝔣, hχ⟩

private theorem exists_common_modulus {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {𝔣₁ 𝔣₂ : Ideal (𝓞 K)}
    (h₁ : HeckeCharacter.AdmitsModulus K χ₁ 𝔣₁) (h₂ : HeckeCharacter.AdmitsModulus K χ₂ 𝔣₂) :
    ∃ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus K χ₁ 𝔪 ∧ HeckeCharacter.AdmitsModulus K χ₂ 𝔪 := by
  obtain ⟨𝔪₁, hm₁, hχ₁⟩ := exists_ne_bot_admitsModulus h₁
  obtain ⟨𝔪₂, hm₂, hχ₂⟩ := exists_ne_bot_admitsModulus h₂
  have hmul : 𝔪₁ * 𝔪₂ ≠ ⊥ := fun h => by
    rcases Ideal.mul_eq_bot.mp h with h | h
    · exact hm₁ h
    · exact hm₂ h
  refine ⟨𝔪₁ * 𝔪₂, hmul, ?_, ?_⟩
  · exact admitsModulus_of_forall_le hχ₁ (idealMultiplicity_le_of_dvd hmul (dvd_mul_right 𝔪₁ 𝔪₂))
  · exact admitsModulus_of_forall_le hχ₂ (idealMultiplicity_le_of_dvd hmul (dvd_mul_left 𝔪₂ 𝔪₁))

end Reduction

end

theorem solution
    (K : Type*) [Field K] [NumberField K]
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχ₁ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ₁)
    (hχ₂ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ₂)
    (hc₁ : Continuous χ₁)
    (hc₂ : Continuous χ₂)
    (𝔣₁ 𝔣₂ : Ideal (𝓞 K))
    (hmod₁ : HeckeCharacter.AdmitsModulus K χ₁ 𝔣₁)
    (hmod₂ : HeckeCharacter.AdmitsModulus K χ₂ 𝔣₂)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S,
      χ₁ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
          (NumberField.AdelicLevel.localUnit (𝓞 K) K v (NumberField.AdelicLevel.uniformizerUnit K v)))
        = χ₂ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
          (NumberField.AdelicLevel.localUnit (𝓞 K) K v (NumberField.AdelicLevel.uniformizerUnit K v)))) :
    χ₁ = χ₂ := by
  obtain ⟨𝔪, hm, hmod₁', hmod₂'⟩ := exists_common_modulus hmod₁ hmod₂
  have hθ : χ₁ * χ₂⁻¹ = 1 := by
    refine ideleChar_eq_one K (χ₁ * χ₂⁻¹) (hc₁.mul hc₂.inv) ?_ 𝔪 hm ?_ S ?_
    · intro u
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ₁ u, hχ₂ u, inv_one, mul_one]
    · intro u h1 h2
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hmod₁' u h1 h2, hmod₂' u h1 h2, inv_one, mul_one]
    · intro v hv
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hS v hv, mul_inv_cancel]
  exact mul_inv_eq_one.mp hθ

end S_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq
end P2MW
export P2MW.S_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq (solution)
