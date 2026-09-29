-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f4cdf23d-88eb-5442-bf73-c43d78510c34

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_injective
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 halfModulus3 torusChar3 principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 LocalGL3 card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

namespace PrincipalSeriesSchur

variable (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private noncomputable def evalOne : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ :=
  (LinearMap.proj (1 : LocalGL3 v)).comp (principalSeries3 v χ).subtype

private theorem evalOne_apply (f : ↥(principalSeries3 v χ)) :
    evalOne v χ f = (f : LocalGL3 v → ℂ) 1 := rfl

variable {v χ}

private theorem translate_apply_one (f : LocalGL3 v → ℂ) (g : LocalGL3 v) :
    gl3AmbientRightTranslate (R := ℂ) g f 1 = f g := by
  rw [gl3AmbientRightTranslate_apply, one_mul]

private theorem apply_upperUnipotent3 {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (x y z : v.adicCompletion ℚ) : f (upperUnipotent3 x y z) = f 1 := by
  have h := apply_upperUnipotent3_mul_of_mem_principalSeries3 hf x y z 1
  rwa [mul_one] at h

private theorem apply_diagonal3 {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    f (diagonal3 v a) = torusChar3 v χ a * halfModulus3 v a * f 1 := by
  have h := apply_diagonal3_mul_of_mem_principalSeries3 hf a 1
  rwa [mul_one] at h

private theorem halfModulus3_ne_zero (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : halfModulus3 v a ≠ 0 := by
  unfold halfModulus3
  exact Complex.ofReal_ne_zero.mpr
    (div_ne_zero (norm_ne_zero_iff.mpr (a 0).ne_zero) (norm_ne_zero_iff.mpr (a 2).ne_zero))

private theorem torusChar3_mulSingle (χ' : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (i : Fin 3)
    (x : (v.adicCompletion ℚ)ˣ) : torusChar3 v χ' (Pi.mulSingle i x) = ((χ' i x : ℂˣ) : ℂ) := by
  unfold torusChar3
  rw [Finset.prod_eq_single i]
  · rw [Pi.mulSingle_eq_same]
  · intro j _ hj
    rw [Pi.mulSingle_eq_of_ne hj, map_one, Units.val_one]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem setOf_perm_subset_singleton (hreg : Function.Injective χ) :
    {w : Equiv.Perm (Fin 3) | ∀ a : Fin 3 → (v.adicCompletion ℚ)ˣ,
        torusChar3 v χ a * halfModulus3 v a = torusChar3 v (χ ∘ ⇑w) a * halfModulus3 v a} ⊆ {1} := by
  intro w hw
  rw [Set.mem_setOf_eq] at hw
  rw [Set.mem_singleton_iff]
  have hχ : ∀ i, χ (w i) = χ i := by
    intro i
    refine MonoidHom.ext fun x => Units.ext ?_
    have h := mul_right_cancel₀ (halfModulus3_ne_zero (Pi.mulSingle i x)) (hw (Pi.mulSingle i x))
    rw [torusChar3_mulSingle, torusChar3_mulSingle, Function.comp_apply] at h
    exact h.symm
  exact Equiv.ext fun i => by rw [Equiv.Perm.one_apply]; exact hreg (hχ i)

end PrincipalSeriesSchur

end LanglandsTunnell.CubicInduction

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_injective.LanglandsTunnell.CubicInduction.PrincipalSeriesSchur"

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hreg : Function.Injective χ)
    (T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hT : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (T f)) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  classical

  have h1 : ∀ (f : ↥(principalSeries3 v χ)) (g : LocalGL3 v),
      (T f : LocalGL3 v → ℂ) g =
        (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ :
          LocalGL3 v → ℂ) 1 := by
    intro f g
    rw [hT g f, translate_apply_one]
  by_cases h0 : evalOne v χ = 0
  ·
    have hz : ∀ (f : ↥(principalSeries3 v χ)) (g : LocalGL3 v), (f : LocalGL3 v → ℂ) g = 0 := by
      intro f g
      have h := LinearMap.congr_fun h0
        ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩
      change gl3AmbientRightTranslate (R := ℂ) g (f : LocalGL3 v → ℂ) 1 = 0 at h
      rwa [translate_apply_one] at h
    refine ⟨0, LinearMap.ext fun f => ?_⟩
    rw [zero_smul, LinearMap.zero_apply]
    exact Subtype.ext (funext fun g => hz (T f) g)
  ·

    have hdep : ¬ LinearIndependent ℂ ![evalOne v χ, (evalOne v χ).comp T] := by
      intro hli
      have hne : evalOne v χ ≠ (evalOne v χ).comp T := by
        intro h
        have h10 := (LinearIndependent.pair_iff.mp hli) 1 (-1)
          (by rw [one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero]; exact h)
        exact one_ne_zero h10.1
      have hind : LinearIndependent ℂ
          (fun Λ : ↥({evalOne v χ, (evalOne v χ).comp T} : Finset (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) =>
            (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) :=
        hli.linearIndepOn_id' ((Matrix.range_cons_cons_empty _ _ _).trans Finset.coe_pair.symm)
      have hle := card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3 v χ
        (fun a => torusChar3 v χ a * halfModulus3 v a) {evalOne v χ, (evalOne v χ).comp T} ?_ ?_ hind
      · rw [Finset.card_pair hne] at hle
        have hle1 := (Set.ncard_le_ncard (setOf_perm_subset_singleton (v := v) (χ := χ) hreg)).trans_eq
          (Set.ncard_singleton _)
        exact absurd (hle.trans hle1) (by decide)
      · intro Λ hΛ x y z f
        rcases Finset.mem_insert.mp hΛ with rfl | hΛ
        · change gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) (f : LocalGL3 v → ℂ) 1 =
            (f : LocalGL3 v → ℂ) 1
          rw [translate_apply_one, apply_upperUnipotent3 f.2]
        · rw [Finset.mem_singleton] at hΛ
          subst hΛ
          change (T ⟨_, _⟩ : LocalGL3 v → ℂ) 1 = (T f : LocalGL3 v → ℂ) 1
          rw [← h1, apply_upperUnipotent3 (T f).2]
      · intro Λ hΛ a f
        rcases Finset.mem_insert.mp hΛ with rfl | hΛ
        · change gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) (f : LocalGL3 v → ℂ) 1 =
            torusChar3 v χ a * halfModulus3 v a * (f : LocalGL3 v → ℂ) 1
          rw [translate_apply_one, apply_diagonal3 f.2]
        · rw [Finset.mem_singleton] at hΛ
          subst hΛ
          change (T ⟨_, _⟩ : LocalGL3 v → ℂ) 1 = torusChar3 v χ a * halfModulus3 v a * (T f : LocalGL3 v → ℂ) 1
          rw [← h1, apply_diagonal3 (T f).2]
    rw [LinearIndependent.pair_iff' h0] at hdep
    obtain ⟨c, hc⟩ := not_forall.mp hdep
    have hc' : c • evalOne v χ = (evalOne v χ).comp T := not_ne_iff.mp hc
    refine ⟨c, LinearMap.ext fun f => Subtype.ext (funext fun g => ?_)⟩
    rw [h1 f g, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    have h2 := LinearMap.congr_fun hc'
      ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩
    change c * gl3AmbientRightTranslate (R := ℂ) g (f : LocalGL3 v → ℂ) 1 = (T ⟨_, _⟩ : LocalGL3 v → ℂ) 1 at h2
    rw [translate_apply_one] at h2
    exact h2.symm

end S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_injective
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_injective (solution)
