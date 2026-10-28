-- Prove2me | solution 1 for OAI.Kadison.NormalGNS.image_bicommutant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:39:38.830972+00:00
-- url     : https://prove2.me/submissions/ea4704f8-9d37-4bc8-a665-28c7e903c186

import Mathlib
import Definitions.Def_OAIQ039C049
import Definitions.Def_OAIQ039C060

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyNet
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.Kaplansky

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))

variable (T : H →L[ℂ] H)
  (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) (hnT : ‖T‖≤1)

include hS hT hnT

lemma approximationNet_spec (j : Finset H × ℕ) :
    approximationNet S hS T hT hnT j∈S ∧ ‖approximationNet S hS T hT hnT j‖≤1 ∧
      ∀ x∈j.1,‖approximationNet S hS T hT hnT j x-T x‖<(j.2+1:ℝ)⁻¹ :=
  (net_approx_exists S hS T hT hnT j).choose_spec

lemma approximationNet_tendsto (x : H) :
    Tendsto (fun j => approximationNet S hS T hT hnT j x) atTop (𝓝 (T x)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop (({x}:Finset H),N)] with j hj
  rw [dist_eq_norm]
  have hxj : x∈j.1 := hj.1 (Finset.mem_singleton_self x)
  apply (approximationNet_spec S hS T hT hnT j).2.2 x hxj |>.trans_le
  have hnj : (N+1:ℝ)≤j.2+1 := by exact_mod_cast Nat.succ_le_succ hj.2
  exact (inv_anti₀ (by positivity) hnj).trans (by simpa only [one_div] using hN.le)

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalGNSClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

open Filter

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hnormal : BoundedWOTContinuous M τ)
  (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))
  (hSM : S≤M.toStarSubalgebra)
  (N : VonNeumannAlgebra τ.GNS)
  (hSN : ∀ a : M,(a:H →L[ℂ] H)∈S → τ.gnsStarAlgHom a∈N)

include hnormal hS hSM hSN in
lemma contraction_image_bicommutant (a : M)
    (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hna : ‖a‖≤1) : τ.gnsStarAlgHom a∈N := by
  classical
  let net := Kaplansky.approximationNet S hS (a:H →L[ℂ] H) ha hna
  have hnet (j : Finset H × ℕ) := Kaplansky.approximationNet_spec S hS (a:H →L[ℂ] H) ha hna j
  let u : Finset H × ℕ → M := fun j => ⟨net j,hSM (hnet j).1⟩
  have hu : ∀ j,‖u j‖≤1 := fun j => (hnet j).2.1
  have hlim (x y : H) : Tendsto (fun j => inner ℂ ((u j:H →L[ℂ] H) x) y) atTop
      (𝓝 (inner ℂ ((a:H →L[ℂ] H) x) y)) :=
    (Kaplansky.approximationNet_tendsto S hS (a:H →L[ℂ] H) ha hna x).inner tendsto_const_nhds
  have hgns (x y : τ.GNS) : Tendsto (fun j => inner ℂ (τ.gnsStarAlgHom (u j) x) y) atTop
      (𝓝 (inner ℂ (τ.gnsStarAlgHom a x) y)) := by
    simpa only [RCLike.star_def,inner_conj_symm] using
      (tendsto_gns M τ hnormal u a 1 hu hna hlim y x).star
  exact WeakOperatorLimit.mem_vonNeumann hgns N (Eventually.of_forall fun j => hSN (u j) (hnet j).1)

include hnormal hS hSM hSN in
lemma image_bicommutant_oai (a : M)
    (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    τ.gnsStarAlgHom a∈N := by
  by_cases hz : a=0
  · subst a
    exact hSN 0 S.zero_mem
  let c : ℂ := (‖a‖:ℂ)
  have hc : c≠0 := by
    dsimp [c]
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  let b : M := c⁻¹ • a
  have hb : (b:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
    intro x hx
    change x*(c⁻¹ • (a:H →L[ℂ] H))=(c⁻¹ • (a:H →L[ℂ] H))*x
    rw [mul_smul_comm,smul_mul_assoc,ha x hx]
  have hnb : ‖b‖≤1 := by
    change ‖c⁻¹ • a‖≤1
    rw [norm_smul,norm_inv]
    change ‖(‖a‖:ℂ)‖⁻¹ * ‖a‖≤1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg a),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  have hN := contraction_image_bicommutant M τ hnormal S hS hSM N hSN b hb hnb
  have hab : c • b=a := by dsimp [b]; rw [smul_smul,mul_inv_cancel₀ hc,one_smul]
  rw [←hab]
  exact (N.toStarSubalgebra.comap τ.gnsStarAlgHom).smul_mem hN c

end Kadison.NormalGNS

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.NormalGNS.image_bicommutant_oai.{u_1} := @OAI.Kadison.NormalGNS.image_bicommutant_oai.{u_1}
