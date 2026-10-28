-- Prove2me | solution 1 for OAI.Kadison.PositiveWOT.exists_injective_inverse_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:07:30.346157+00:00
-- url     : https://prove2.me/submissions/1d0b1f78-ea4d-451f-a189-4c12f941f3d1

import Mathlib
import Definitions.Def_OAIQ039C003

section
-- module Solutions.OAIQ039_CM.Commutator_PositiveCauchySchwarz
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sqrt_inner (A : H →L[ℂ] H) (ha : 0≤A) (x y : H) :
    inner ℂ (CFC.sqrt A x) (CFC.sqrt A y)=inner ℂ (A x) y := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A))
  have he := hs (CFC.sqrt A x) y
  have hh : CFC.sqrt A*CFC.sqrt A=A := by simpa only [pow_two] using CFC.sq_sqrt A ha
  change inner ℂ ((CFC.sqrt A*CFC.sqrt A) x) y=
    inner ℂ (CFC.sqrt A x) (CFC.sqrt A y) at he
  exact he.symm.trans (congrArg (fun T : H →L[ℂ] H => inner ℂ (T x) y) hh)

lemma sqrt_norm_sq (A : H →L[ℂ] H) (ha : 0≤A) (x : H) :
    ‖CFC.sqrt A x‖^2=(inner ℂ (A x) x).re := by
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),sqrt_inner A ha x x]
  rfl

lemma positive_cauchySchwarz (A : H →L[ℂ] H) (ha : 0≤A) (x y : H) :
    ‖inner ℂ (A x) y‖^2≤(inner ℂ (A x) x).re*(inner ℂ (A y) y).re := by
  have hh := norm_inner_le_norm (𝕜:=ℂ) (CFC.sqrt A x) (CFC.sqrt A y)
  have hs := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hh
  rw [mul_pow,sqrt_norm_sq A ha x,sqrt_norm_sq A ha y,sqrt_inner A ha x y] at hs
  exact hs

lemma inverse_cauchySchwarz (A : (H →L[ℂ] H)ˣ) (ha : 0≤(A:H →L[ℂ] H)) (x y : H) :
    ‖inner ℂ x y‖^2≤(inner ℂ ((↑A⁻¹:H →L[ℂ] H) x) x).re*(inner ℂ ((A:H →L[ℂ] H) y) y).re := by
  have hh := positive_cauchySchwarz (A:H →L[ℂ] H) ha ((↑A⁻¹:H →L[ℂ] H) x) y
  have he : (A:H →L[ℂ] H) ((↑A⁻¹:H →L[ℂ] H) x)=x := by
    change ((A:H →L[ℂ] H)*(↑A⁻¹:H →L[ℂ] H)) x=x
    rw [Units.mul_inv,one_apply_eq_self]
  rw [he] at hh
  have hre : (inner ℂ x ((↑A⁻¹:H →L[ℂ] H) x)).re=
      (inner ℂ ((↑A⁻¹:H →L[ℂ] H) x) x).re := inner_re_symm (𝕜:=ℂ) _ _
  rw [hre] at hh
  exact hh

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PositiveWOT
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma inner_mono {A B : H →L[ℂ] H} (h : A≤B) (x : H) :
    (inner ℂ (A x) x).re≤(inner ℂ (B x) x).re := by
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr h)
  have hh : 0≤(inner ℂ ((B-A) x) x).re := hp.re_inner_nonneg_left x
  simpa only [sub_apply,inner_sub_left,Complex.sub_re,sub_nonneg] using hh

omit [CompleteSpace H] in
lemma nonneg_limit {l : Filter I} [l.NeBot] {T : I → H →L[ℂ] H} {W : H →L[ℂ] H}
    (ht : ∀ x y,Tendsto (fun i => inner ℂ (T i x) y) l (𝓝 (inner ℂ (W x) y)))
    (hp : ∀ᶠ i in l,0≤T i) : 0≤W := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  have hh : 0 ≤ inner ℂ (W x) x := ge_of_tendsto (ht x x) (hp.mono fun i hi =>
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hi).inner_nonneg_left x)
  exact ⟨Complex.ext (by simp) (by simpa using hh.2),hh.1⟩

lemma limit_le {l : Filter I} [l.NeBot] {T : I → H →L[ℂ] H} {W A : H →L[ℂ] H}
    (ht : ∀ x y,Tendsto (fun i => inner ℂ (T i x) y) l (𝓝 (inner ℂ (W x) y)))
    (hp : ∀ᶠ i in l,T i≤A) : W≤A := by
  apply sub_nonneg.mp
  refine nonneg_limit (T:=fun i => A-T i) ?_ (hp.mono fun _ hi => sub_nonneg.mpr hi)
  intro x y
  simpa only [sub_apply,inner_sub_left] using
    ((tendsto_const_nhds (x:=inner ℂ (A x) y)).sub (ht x y))

lemma contraction_square_le {A : H →L[ℂ] H} (ha : 0≤A) (h1 : A≤1) : A*A≤A := by
  have hc : Commute A (1-A) := (Commute.one_right A).sub_right (Commute.refl A)
  have hh := hc.mul_nonneg ha (sub_nonneg.mpr h1)
  have he : A*(1-A)=A-A*A := by noncomm_ring
  rw [he] at hh
  exact sub_nonneg.mp hh

lemma contraction_norm_sq_le {A : H →L[ℂ] H} (ha : 0≤A) (h1 : A≤1) (x : H) :
    ‖A x‖^2≤(inner ℂ (A x) x).re := by
  have hh := inner_mono (contraction_square_le ha h1) x
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (IsSelfAdjoint.of_nonneg ha)
  have he : inner ℂ ((A*A) x) x=inner ℂ (A x) (A x) := hs (A x) x
  rw [he] at hh
  rw [norm_sq_eq_re_inner (𝕜:=ℂ)]
  exact hh

theorem exists_strong_inf (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hPM : ∀ n,P n∈M) (hpos : ∀ n,0≤P n) (hone : ∀ n,P n≤1) (hmono : Antitone P) :
    ∃ B : H →L[ℂ] H,B∈M ∧ 0≤B ∧ B≤1 ∧ (∀ n,B≤P n) ∧
      (∀ x,Tendsto (fun n => P n x) atTop (𝓝 (B x))) := by
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ)≤atTop := Ultrafilter.of_le atTop
  obtain ⟨B,hBn,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω P 1 zero_le_one
    (fun n => (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hpos n)).mpr (hone n))
  have hBpos : 0≤B := nonneg_limit hlim (Eventually.of_forall hpos)
  have hB1 : B≤1 := limit_le hlim (Eventually.of_forall hone)
  have hBP (n : ℕ) : B≤P n := limit_le hlim
    (((eventually_ge_atTop n).filter_mono hω).mono fun m hnm => hmono hnm)
  refine ⟨B,WeakOperatorLimit.mem_vonNeumann hlim M (Eventually.of_forall hPM),hBpos,hB1,hBP,?_⟩
  intro x
  have hscalar : Tendsto (fun n => (inner ℂ ((P n-B) x) x).re) (ω : Filter ℕ) (𝓝 0) := by
    simpa only [sub_apply,inner_sub_left,Complex.sub_re,Function.comp_apply,sub_self]
      using (Complex.continuous_re.tendsto _ |>.comp (hlim x x)).sub (tendsto_const_nhds (x:=(inner ℂ (B x) x).re))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := (hscalar.eventually_lt_const (sq_pos_of_pos hε)).exists
  refine ⟨N,?_⟩
  intro n hn
  have hDpos : 0≤P n-B := sub_nonneg.mpr (hBP n)
  have hD1 : P n-B≤1 := (sub_le_self _ hBpos).trans (hone n)
  have hsq := contraction_norm_sq_le hDpos hD1 x
  have hle := inner_mono (sub_le_sub_right (hmono hn) B) x
  have hlt : ‖(P n-B) x‖<ε := by nlinarith [norm_nonneg ((P n-B) x)]
  simpa only [dist_eq_norm,sub_apply] using hlt

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InverseLimit
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma units_inverse_mem (M : VonNeumannAlgebra H) (A : (H →L[ℂ] H)ˣ)
    (hA : (A:H →L[ℂ] H)∈M) : (↑A⁻¹:H →L[ℂ] H)∈M := by
  change (↑A⁻¹:H →L[ℂ] H)∈M.carrier
  rw [←M.centralizer_centralizer']
  intro T hT
  exact (show Commute (A:H →L[ℂ] H) T from hT _ hA).units_inv_left.eq.symm

theorem exists_injective_inverse_limit_oai (M : VonNeumannAlgebra H)
    (S : ℕ → H →L[ℂ] H) (hSM : ∀ n,S n∈M) (hone : ∀ n,1≤S n)
    (hmono : Monotone S) (v : J → H) (hdense : DenseRange v)
    (hbounded : ∀ j,∃ C : ℝ,∀ n,(inner ℂ (S n (v j)) (v j)).re≤C) :
    ∃ B : H →L[ℂ] H,B∈M ∧ 0≤B ∧ B≤1 ∧ Function.Injective B ∧
      (∀ n,B≤Ring.inverse (S n)) ∧
      (∀ x,Tendsto (fun n => Ring.inverse (S n) x) atTop (𝓝 (B x))) := by
  let U (n : ℕ) : (H →L[ℂ] H)ˣ := (CStarAlgebra.isUnit_of_le 1 (hone n)).unit
  have hu (n : ℕ) : (U n:H →L[ℂ] H)=S n := IsUnit.unit_spec _
  have hp (n : ℕ) : 0≤(U n:H →L[ℂ] H) := by rw [hu]; exact zero_le_one.trans (hone n)
  let P (n : ℕ) : H →L[ℂ] H := (↑(U n)⁻¹:H →L[ℂ] H)
  have hPeq (n : ℕ) : P n=Ring.inverse (S n) := by rw [←hu,Ring.inverse_unit]
  have hPM (n : ℕ) : P n∈M := units_inverse_mem M (U n) (by rw [hu]; exact hSM n)
  have hPpos (n : ℕ) : 0≤P n := CFC.inv_nonneg_of_nonneg (U n) (hp n)
  have hPone (n : ℕ) : P n≤1 := CStarAlgebra.inv_le_one (by change (1:H →L[ℂ] H)≤(U n:H →L[ℂ] H); rw [hu]; exact hone n)
  have hPmono : Antitone P := by
    intro n m hnm
    exact CStarAlgebra.inv_le_inv (hp n) (by rw [hu,hu]; exact hmono hnm)
  obtain ⟨B,hBM,hBpos,hB1,hBP,hlim⟩ := exists_strong_inf M P hPM hPpos hPone hPmono
  have hker : ∀ x,B x=0 → x=0 := by
    intro x hx
    have hin (j : J) : inner ℂ x (v j)=0 := by
      obtain ⟨C,hC⟩ := hbounded j
      have hh (n : ℕ) : ‖inner ℂ x (v j)‖^2≤(inner ℂ (P n x) x).re*C := by
        have hcs := inverse_cauchySchwarz (U n) (hp n) x (v j)
        rw [hu] at hcs
        exact hcs.trans (mul_le_mul_of_nonneg_left (hC n)
          (((ContinuousLinearMap.nonneg_iff_isPositive _).mp (hPpos n)).re_inner_nonneg_left x))
      have ht : Tendsto (fun n => (inner ℂ (P n x) x).re*C) atTop (𝓝 0) := by
        have hh := (Complex.continuous_re.tendsto _ |>.comp
          ((hlim x).inner (tendsto_const_nhds (x:=x)))).mul_const C
        simpa only [hx,inner_zero_left,Complex.zero_re,zero_mul,Function.comp_apply] using hh
      have hz : ‖inner ℂ x (v j)‖^2≤0 := ge_of_tendsto ht (Eventually.of_forall hh)
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (inner ℂ x (v j))])
    apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    exact hdense.induction_on (p:=fun y => inner ℂ x y=0) x
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const) hin
  refine ⟨B,hBM,hBpos,hB1,?_,?_,?_⟩
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hker
    simp only [map_sub,hxy,sub_self]
  · intro n; rw [←hPeq]; exact hBP n
  · intro x; simpa only [hPeq] using hlim x

end Kadison.PositiveWOT

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.PositiveWOT.exists_injective_inverse_limit_oai.{u_1, u_2} := @OAI.Kadison.PositiveWOT.exists_injective_inverse_limit_oai.{u_1, u_2}
