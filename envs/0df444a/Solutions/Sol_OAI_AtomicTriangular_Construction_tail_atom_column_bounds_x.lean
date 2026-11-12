-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.tail_atom_column_bounds_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:34:46.892322+00:00
-- url     : https://prove2.me/submissions/eef7f59c-59de-43d8-b782-3fb4a87bed33

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X004

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_Analytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma wavePhase_re (k v t : ℝ) : (I*Real.pi*zeta k v t).re = -Real.pi*(k*Xwave k t-v) := by
  simp [zeta,mul_re,mul_im]

lemma Xwave_antitone {k s t : ℝ} (hk : 0<k) (hs : 0 ≤ s) (hst : s ≤ t) :
    Xwave k t≤Xwave k s := by
  unfold Xwave
  apply div_le_div_of_nonneg_left (by norm_num) (waveDen_pos hk s)
  unfold waveDen
  nlinarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_JetEnvelopeAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex
namespace AtomicTriangular.Construction
lemma norm_transformedWave (k v t : ℝ) (n : ℤ) :
    ‖transformedWave k v t n‖ = ‖lambda k t‖ * Real.exp (-frequencyDecay k v t*n) := by
  rw [transformedWave,norm_mul,Complex.norm_exp]
  congr 2
  rw [show I*Real.pi*zeta k v t*(n:ℂ) = (I*Real.pi*zeta k v t)*(n:ℂ) by rfl,
    Complex.mul_re,Complex.intCast_re,Complex.intCast_im,mul_zero,sub_zero,wavePhase_re]
  unfold frequencyDecay
  ring
lemma jetMultiplier_pair_bound (k v t : ℝ) (n : ℤ) (hQ : 0<Q n) :
    (∑ d : Fin 2, ‖jetMultiplier k v n d t‖) ≤ normJetEnvelope k v n t := by
  have hqi : ‖(Q n:ℂ)⁻¹‖=(Q n)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ]
  have hb : ‖(D n:ℂ)-I*Real.pi*zeta k v t‖ ≤ |D n|+‖I*Real.pi*zeta k v t‖ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using norm_sub_le (D n:ℂ) (I*Real.pi*zeta k v t)
  simp only [Fin.sum_univ_two,jetMultiplier,Fin.val_zero,Fin.val_one,one_ne_zero,
    ↓reduceIte,norm_mul,norm_neg,norm_one,mul_one,hqi,norm_transformedWave]
  calc
    _ ≤ (Q n)⁻¹*(‖lambda k t‖*Real.exp (-frequencyDecay k v t*n)) +
        (Q n)⁻¹*(‖lambda k t‖*Real.exp (-frequencyDecay k v t*n))*(|D n|+‖I*Real.pi*zeta k v t‖) := by
      gcongr
    _ = _ := by unfold normJetEnvelope; ring
lemma jet_pair_bound (k v : ℝ) (n : ℤ) (hQ : 0<Q n) (S : Fin 31 → ℂ) :
    (∑ d : Fin 2, |jet k v n d S|) ≤
      ∑ j : Fin 31, normJetEnvelope k v n (frequency j)*‖S j‖ := by
  calc
    _ ≤ ∑ d : Fin 2, ∑ j : Fin 31, ‖jetMultiplier k v n d (frequency j)‖*‖S j‖ := by
      apply Finset.sum_le_sum
      intro d _
      apply (Complex.abs_re_le_norm _).trans
      simpa only [norm_mul] using norm_sum_le (s:=Finset.univ)
        (fun j : Fin 31 => jetMultiplier k v n d (frequency j)*S j)
    _ = ∑ j : Fin 31, (∑ d : Fin 2, ‖jetMultiplier k v n d (frequency j)‖)*‖S j‖ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (jetMultiplier_pair_bound k v (frequency j) n hQ) (norm_nonneg _))
lemma normJetEnvelope_nonneg (k v t : ℝ) (n : ℤ) (hQ : 0<Q n) :
    0≤normJetEnvelope k v n t := by unfold normJetEnvelope; positivity
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_TailEnvelopeSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma frequencyDecay_pos (q v : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    0 < frequencyDecay (damping q) (damping v) t := by
  have hx := Xwave_antitone (damping_pos q) (abs_nonneg t) ht
  have he : Xwave (damping q) |t|=Xwave (damping q) t := by simp [Xwave,waveDen,sq_abs]
  rw [he] at hx
  have hb : damping v < damping q * Xwave (damping q) (5/6) := by
    fin_cases q <;> fin_cases v <;> (first | (simp [damping,h,H,Xwave,waveDen]; all_goals first | (norm_num [damping,h,H,Xwave,waveDen]; done) | rfl | decide) | (norm_num [damping,h,H,Xwave,waveDen]; done) | norm_num [damping,h,H,Xwave,waveDen])
  unfold frequencyDecay
  exact mul_pos Real.pi_pos (sub_pos.mpr (hb.trans_le (mul_le_mul_of_nonneg_left hx (damping_pos q).le)))
lemma normJetEnvelope_enumerateTail (a : Fin 15) (l : ℕ) (k v t : ℝ) :
    normJetEnvelope k v (enumerateTail (a,l)).val.val t =
      normJetEnvelope k v (tailBase a) t * (Real.exp (-frequencyDecay k v t*36))^l := by
  unfold normJetEnvelope
  rw [Q_enumerateTail,D_enumerateTail]
  change _ * Real.exp (-frequencyDecay k v t * ((tailBase a + 36*(l:ℤ):ℤ):ℝ)) = _
  rw [show -frequencyDecay k v t * ((tailBase a + 36*(l:ℤ):ℤ):ℝ) =
    -frequencyDecay k v t*(tailBase a:ℝ) + (l:ℝ)*(-frequencyDecay k v t*36) by push_cast; ring,
    Real.exp_add,Real.exp_nat_mul]
  ring
lemma summable_envelope_period (q v : Fin 2) (a : Fin 15) {t : ℝ} (ht : |t|≤5/6) :
    Summable (fun l : ℕ => normJetEnvelope (damping q) (damping v) (enumerateTail (a,l)).val.val t) := by
  simp_rw [normJetEnvelope_enumerateTail]
  apply Summable.mul_left
  apply summable_geometric_of_norm_lt_one
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
  have hh := frequencyDecay_pos q v ht
  nlinarith
lemma tsum_envelope_period (q v : Fin 2) (a : Fin 15) {t : ℝ} (ht : |t|≤5/6) :
    (∑' l : ℕ, normJetEnvelope (damping q) (damping v) (enumerateTail (a,l)).val.val t) =
    normJetEnvelope (damping q) (damping v) (tailBase a) t *
      (1-Real.exp (-frequencyDecay (damping q) (damping v) t*36))⁻¹ := by
  simp_rw [normJetEnvelope_enumerateTail]
  rw [tsum_mul_left,tsum_geometric_of_norm_lt_one]
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
  have hh := frequencyDecay_pos q v ht
  nlinarith
lemma summable_tailEnvelope (q v : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    Summable (fun n : TailNode => normJetEnvelope (damping q) (damping v) n.val.val t) := by
  apply (tailEnumeration.summable_iff).mp
  apply (summable_prod_of_nonneg (fun p => normJetEnvelope_nonneg _ _ _ _ (by
    have hh := FiniteCertificate.Q_node_bounds (enumerateTail p).val.val (enumerateTail p).val.property.2
    change 0 < Q (enumerateTail p).val.val
    linarith [hh.1]))).mpr
  exact ⟨fun a => summable_envelope_period q v a ht, (hasSum_fintype _).summable⟩
lemma tsum_tailEnvelope (q v : Fin 2) (j : Fin 31) :
    (∑' n : TailNode, normJetEnvelope (damping q) (damping v) n.val.val (frequency j)) =
    tailEnvelopeSum q v j := by
  have ht : |frequency j|≤5/6 := abs_le.mpr (frequency_mem j)
  rw [←tailEnumeration.tsum_eq]
  have hs := tailEnumeration.summable_iff.mpr (summable_tailEnvelope q v ht)
  change Summable (fun p : Fin 15 × ℕ => normJetEnvelope (damping q) (damping v) (enumerateTail p).val.val (frequency j)) at hs
  change (∑' p : Fin 15 × ℕ, normJetEnvelope (damping q) (damping v) (enumerateTail p).val.val (frequency j)) = _
  rw [hs.tsum_prod]
  simp_rw [tsum_envelope_period q v _ ht]
  rw [tsum_fintype,←Finset.sum_mul]
  rfl
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_KernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma Node.Qpos (n : Node) : 0<Q n.val := by
  have hh := FiniteCertificate.Q_node_bounds _ n.property.2
  linarith [hh.1]
lemma tail_atom_column_bounds_x_oai (q v : Fin 2) (S : Fin 31 → ℂ) :
    Summable (fun p : TailNode × Fin 2 => |jet (damping q) (damping v) p.1.val.val p.2 S|) ∧
    (∑' p : TailNode × Fin 2, |jet (damping q) (damping v) p.1.val.val p.2 S|)  ≤ 
      ∑ j : Fin 31, tailEnvelopeSum q v j*‖S j‖ := by
  have hs (j : Fin 31) : Summable (fun n : TailNode =>
      normJetEnvelope (damping q) (damping v) n.val.val (frequency j)*‖S j‖) :=
    (summable_tailEnvelope q v (abs_le.mpr (frequency_mem j))).mul_right _
  have hsum := summable_sum (s:=Finset.univ) (fun j _ => hs j)
  have hh := paired_summable_bound (fun n d => jet (damping q) (damping v) n.val.val d S)
    (fun n : TailNode => ∑ j : Fin 31, normJetEnvelope (damping q) (damping v) n.val.val (frequency j)*‖S j‖)
    hsum (fun n => jet_pair_bound _ _ _ n.val.Qpos S)
  refine ⟨hh.1,?_⟩
  calc
    _  ≤  _ := hh.2
    _ = _ := by
      rw [Summable.tsum_finsetSum (fun j _ => hs j)]
      simp only [tsum_mul_right,tsum_tailEnvelope]
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.tail_atom_column_bounds_x_oai := @OAI.AtomicTriangular.Construction.tail_atom_column_bounds_x_oai
