-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_08
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T05:55:34.594569+00:00
-- url     : https://prove2.me/submissions/d198b2ba-4213-4a89-8cff-add4243e61c9

import Definitions.Def_SidorenkoFiniteGeometryCertificates06
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0005]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0007]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0010]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0012]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0021]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0024]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0141]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0142]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem certificate_proof_0182 {A B : Type} [Finite A] [Finite B]
    (f : A → B) (m : ℕ) (h : ∀ b, Nat.card {a : A // f a = b} ≤ m) :
    Nat.card A ≤ Nat.card B * m := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  calc
    Nat.card A = Nat.card (Σ b : B, {a : A // f a = b}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ b : B, Nat.card {a : A // f a = b} := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]
    _ ≤ ∑ _b : B, m := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card B * m := by simp [Nat.card_eq_fintype_card]

private instance certificate_instance_0182 : OAI.SidorenkoCounterexample.ProofCertificate_0182 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0182 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6

section NormSphere
variable {K E : Type} [Field K] [Fintype K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
theorem certificate_proof_0183 (a : K) : Nat.card {x : K // x^2 = a} ≤ 2 := by
  classical
  by_cases h : ∃ x : K, x^2 = a
  · obtain ⟨x,hx⟩ := h
    let f : {z : K // z^2 = a} → (↑({x,-x} : Finset K)) := fun z =>
      ⟨z.val,by
        have hh : z.val = x ∨ z.val = -x := sq_eq_sq_iff_eq_or_eq_neg.mp (z.property.trans hx.symm)
        simpa only [Finset.mem_insert,Finset.mem_singleton] using hh⟩
    have hf : Function.Injective f := by
      intro z w he
      apply Subtype.ext
      exact congrArg (fun t : ↑({x,-x} : Finset K) => (t : K)) he
    calc
      _ ≤ Nat.card (↑({x,-x} : Finset K)) := Nat.card_le_card_of_injective f hf
      _ = ({x,-x} : Finset K).card := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_coe _
      _ ≤ 2 := Finset.card_le_two
  · have he : IsEmpty {x : K // x^2 = a} := ⟨fun x => h ⟨x.val,x.property⟩⟩
    let := he
    simp

private instance certificate_instance_0183 : OAI.SidorenkoCounterexample.ProofCertificate_0183 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0183 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3

omit [FiniteDimensional K E] in
theorem certificate_proof_0184 (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (x : E) (hx : B x x ≠ 0) (a : K) :
    Nat.card {v : E // B v v = a} ≤
      2 * Nat.card (B.orthogonal (K ∙ x)) := by
  classical
  have hx0 : x ≠ 0 := by intro hh; subst x; simp at hx
  let P := B.orthogonal (K ∙ x)
  let c : ((K ∙ x) × P) ≃ₗ[K] E :=
    (K ∙ x).prodEquivOfIsCompl P (B.isCompl_span_singleton_orthogonal hx)
  let e : (K × P) ≃ₗ[K] E :=
    ((LinearEquiv.toSpanNonzeroSingleton K E x hx0).prodCongr (LinearEquiv.refl K P)).trans c
  have he (z : K × P) : e z = z.1 • x + z.2.val := rfl
  have hnorm (z : K × P) : B (e z) (e z) = z.1^2 * B x x + B z.2.val z.2.val := by
    have h1 : B x z.2.val = 0 := z.2.property x (Submodule.mem_span_singleton_self x)
    have h2 : B z.2.val x = 0 := hs.eq _ _ ▸ h1
    rw [he]
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
      smul_eq_mul,h1,h2,mul_zero,add_zero,zero_add]
    ring
  let f : {v : E // B v v = a} → P := fun v => (e.symm v.val).2
  have hf (p : P) : Nat.card {v : {v : E // B v v = a} // f v = p} ≤ 2 := by
    let g : {v : {v : E // B v v = a} // f v = p} →
        {t : K // t^2 = (a - B p.val p.val) / B x x} := fun v =>
      ⟨(e.symm v.val.val).1,by
        have hh := hnorm (e.symm v.val.val)
        have hv : (e.symm v.val.val).2 = p := v.property
        rw [e.apply_symm_apply,v.val.property,hv] at hh
        apply (eq_div_iff hx).mpr
        linear_combination -hh⟩
    have hg : Function.Injective g := by
      intro v w h
      apply Subtype.ext
      apply Subtype.ext
      apply e.symm.injective
      apply Prod.ext
      · exact congrArg Subtype.val h
      · exact v.property.trans w.property.symm
    exact (Nat.card_le_card_of_injective g hg).trans (square_fiber_card _)
  exact (card_le_card_mul_of_fibers f 2 hf).trans_eq (Nat.mul_comm _ _)

private instance certificate_instance_0184 : OAI.SidorenkoCounterexample.ProofCertificate_0184 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0184 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0185 (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (x : E) (hx : B x x ≠ 0) (a : K) :
    Nat.card {v : E // B v v = a} ≤ 2 * Fintype.card K ^ (finrank K E - 1) := by
  have hx0 : x ≠ 0 := by intro hh; subst x; simp at hx
  have hd := Submodule.finrank_add_eq_of_isCompl (B.isCompl_span_singleton_orthogonal hx)
  rw [finrank_span_singleton hx0] at hd
  have hp : finrank K (B.orthogonal (K ∙ x)) = finrank K E - 1 := by omega
  have hc : Nat.card (B.orthogonal (K ∙ x)) = Fintype.card K ^ (finrank K E - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hp, Nat.card_eq_fintype_card]
  exact (norm_sphere_count B hs x hx a).trans_eq (congrArg (2 * ·) hc)

private instance certificate_instance_0185 : OAI.SidorenkoCounterexample.ProofCertificate_0185 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0185 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end NormSphere
section Isometries
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
instance (B : LinearMap.BilinForm K E) [Finite E] : Finite (BilinAut B) := by
  apply Finite.of_injective (fun e : BilinAut B => (e.val : E → E))
  intro e f h
  apply Subtype.ext
  exact LinearEquiv.ext (congrFun h)
theorem certificate_proof_0186 (B : LinearMap.BilinForm K E)
    (x : E) (e : BilinAut B) (hfix : e.val x = x)
    (z : B.orthogonal (K ∙ x)) :
    ((restrictBilinAut B x e hfix).val z).val = e.val z.val := rfl

private instance certificate_instance_0186 : OAI.SidorenkoCounterexample.ProofCertificate_0186 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0186 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0187 (B : LinearMap.BilinForm K E)
    (x : E) (hx : B x x ≠ 0) :
    Function.Injective (fun e : {e : BilinAut B // e.val x = x} =>
      restrictBilinAut B x e.val e.property) := by
  intro e f h
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  have hz : z ∈ (K ∙ x) ⊔ B.orthogonal (K ∙ x) := by
    rw [(B.isCompl_span_singleton_orthogonal hx).sup_eq_top]
    trivial
  obtain ⟨a,ha,p,hp,rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp ha
  have hh := congrArg (fun g : BilinAut (B.restrict (B.orthogonal (K ∙ x))) =>
    (g.val (⟨p,hp⟩ : B.orthogonal (K ∙ x))).val) h
  change e.val.val p = f.val.val p at hh
  simp only [map_add,map_smul,e.property,f.property,hh]

private instance certificate_instance_0187 : OAI.SidorenkoCounterexample.ProofCertificate_0187 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0187 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7 q8

omit [FiniteDimensional K E] in
theorem certificate_proof_0188 (B : LinearMap.BilinForm K E) (f : BilinAut B) :
    Function.Injective (fun e => relativeBilinAut B e f) := by
  intro e g h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hh := congrArg (fun a : BilinAut B => f.val (a.val x)) h
  simpa only [relativeBilinAut,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply] using hh

private instance certificate_instance_0188 : OAI.SidorenkoCounterexample.ProofCertificate_0188 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0188 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6

variable [Finite E]
theorem certificate_proof_0189 (B : LinearMap.BilinForm K E) (x y : E)
    (hx : B x x ≠ 0) :
    Nat.card {e : BilinAut B // e.val x = y} ≤
      Nat.card (BilinAut (B.restrict (B.orthogonal (K ∙ x)))) := by
  classical
  by_cases hn : Nonempty {e : BilinAut B // e.val x = y}
  · let e0 := hn.some
    let f : {e : BilinAut B // e.val x = y} → {e : BilinAut B // e.val x = x} := fun e =>
      ⟨relativeBilinAut B e.val e0.val,by
        change e0.val.val.symm (e.val.val x) = x
        exact (congrArg e0.val.val.symm (e.property.trans e0.property.symm)).trans
          (e0.val.val.symm_apply_apply x)⟩
    have hf : Function.Injective f := by
      intro e g h
      apply Subtype.ext
      apply relativeBilinAut_injective B e0.val
      exact congrArg Subtype.val h
    exact (Nat.card_le_card_of_injective f hf).trans
      (Nat.card_le_card_of_injective _ (restrictBilinAut_injective B x hx))
  · have : IsEmpty {e : BilinAut B // e.val x = y} := not_nonempty_iff.mp hn
    let := this
    simp

private instance certificate_instance_0189 : OAI.SidorenkoCounterexample.ProofCertificate_0189 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0189 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0190 (B : LinearMap.BilinForm K E) (x : E) (hx : B x x ≠ 0) :
    Nat.card (BilinAut B) ≤ Nat.card {y : E // B y y = B x x} *
      Nat.card (BilinAut (B.restrict (B.orthogonal (K ∙ x)))) := by
  let s : BilinAut B → {y : E // B y y = B x x} := fun e => ⟨e.val x,e.property x x⟩
  apply card_le_card_mul_of_fibers s
  intro y
  let f : {e : BilinAut B // s e = y} → {e : BilinAut B // e.val x = y.val} :=
    fun e => ⟨e.val,congrArg Subtype.val e.property⟩
  have hf : Function.Injective f := by
    intro e g h
    apply Subtype.ext
    exact congrArg (fun t : {e : BilinAut B // e.val x = y.val} => t.val) h
  exact (Nat.card_le_card_of_injective f hf).trans (bilinAut_eval_fiber_bound B x y.val hx)

private instance certificate_instance_0190 : OAI.SidorenkoCounterexample.ProofCertificate_0190 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0190 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

variable [Fintype K] [Invertible (2 : K)]
theorem certificate_proof_0191 (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (hB : B.Nondegenerate) :
    Nat.card (BilinAut B) ≤ 2 ^ finrank K E * Fintype.card K ^ (finrank K E).choose 2 := by
  suffices ∀ d, finrank K E = d →
      Nat.card (BilinAut B) ≤ 2 ^ d * Fintype.card K ^ d.choose 2 by exact this _ rfl
  intro d hd
  induction d generalizing E with
  | zero =>
    have : Subsingleton E := Module.finrank_zero_iff.mp hd
    have : Subsingleton (BilinAut B) := by
      refine ⟨fun e f => ?_⟩
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      exact Subsingleton.elim _ _
    simpa using Nat.card_le_card_of_injective (fun _ : BilinAut B => ())
      (fun _ _ _ => Subsingleton.elim _ _)
  | succ d ih =>
    have hB0 : B ≠ 0 := by
      intro hh
      have hz : ∀ x : E, x = 0 := by
        intro x
        apply hB.1
        intro y
        rw [hh]
        rfl
      have hh0 : finrank K E = 0 := (finrank_zero_iff_forall_zero).mpr hz
      omega
    obtain ⟨x,hx⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero hB0 (LinearMap.BilinForm.isSymm_iff.mp hs)
    have hx0 : x ≠ 0 := by intro hh; subst x; simp at hx
    let P := B.orthogonal (K ∙ x)
    have hP : finrank K P = d := by
      change finrank K (B.orthogonal (K ∙ x)) = d
      have hh := Submodule.finrank_add_eq_of_isCompl (B.isCompl_span_singleton_orthogonal hx)
      rw [finrank_span_singleton hx0,hd] at hh
      omega
    have hp := ih (B.restrict P) (by constructor; intro x y; exact hs.eq x.val y.val)
      (B.restrict_nondegenerate_orthogonal_spanSingleton hB hs.isRefl hx) hP
    have hn := norm_sphere_count_pow B hs x hx (B x x)
    rw [hd,Nat.add_sub_cancel] at hn
    calc
      _ ≤ Nat.card {y : E // B y y = B x x} * Nat.card (BilinAut (B.restrict P)) :=
        bilinAut_step B x hx
      _ ≤ (2 * Fintype.card K ^ d) * (2^d * Fintype.card K ^ d.choose 2) :=
        Nat.mul_le_mul hn hp
      _ = 2 ^ (d+1) * Fintype.card K ^ (d+1).choose 2 := by
        rw [Nat.choose_succ_succ,Nat.choose_one_right,pow_add,pow_succ]
        ring

private instance certificate_instance_0191 : OAI.SidorenkoCounterexample.ProofCertificate_0191 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0191 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end Isometries
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FormOrbits
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
theorem certificate_proof_0192 : Function.Bijective (linearAutTuple (K := K) (E := E)) := by
  constructor
  · intro e f h
    apply LinearEquiv.toLinearMap_injective
    apply (finBasis K E).ext
    intro i
    exact congrFun (congrArg Subtype.val h) i
  · intro v
    have hspan : Submodule.span K (Set.range v.val) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card v.property,Fintype.card_fin]
    let b : Basis (Fin (finrank K E)) K E := Basis.mk v.property (by rw [hspan])
    refine ⟨(finBasis K E).equiv b (Equiv.refl _),?_⟩
    apply Subtype.ext
    funext i
    simp [linearAutTuple,b]

private instance certificate_instance_0192 : OAI.SidorenkoCounterexample.ProofCertificate_0192 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0192 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5

variable [Fintype K] [Finite E]
theorem certificate_proof_0193 : Nat.card (E ≃ₗ[K] E) =
    ∏ i : Fin (finrank K E), (Fintype.card K ^ finrank K E - Fintype.card K ^ i.val) := by
  rw [Nat.card_congr (Equiv.ofBijective _ (linearAutTuple_bijective (K := K) (E := E)))]
  exact card_linearIndependent le_rfl

private instance certificate_instance_0193 : OAI.SidorenkoCounterexample.ProofCertificate_0193 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0193 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7

omit [FiniteDimensional K E] [Fintype K] in
theorem certificate_proof_0194 (B : LinearMap.BilinForm K E) (C : FormOrbit B) :
    Nat.card {e : E ≃ₗ[K] E // formOrbitMap B e = C} ≤ Nat.card (BilinAut B) := by
  classical
  obtain ⟨e0,he0⟩ := C.property
  let f : {e : E ≃ₗ[K] E // formOrbitMap B e = C} → BilinAut B := fun e =>
    ⟨e0.symm.trans e.val,by
      intro x y
      have hh := congrArg (fun D : FormOrbit B => D.val (e0.symm x) (e0.symm y)) e.property
      change B (e.val (e0.symm x)) (e.val (e0.symm y)) = C.val (e0.symm x) (e0.symm y) at hh
      rw [he0] at hh
      simpa only [LinearMap.BilinForm.comp_apply,LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply,LinearEquiv.trans_apply] using hh⟩
  apply Nat.card_le_card_of_injective f
  intro e g h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hh := congrArg (fun a : BilinAut B => a.val (e0 x)) h
  simpa only [f,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] using hh

private instance certificate_instance_0194 : OAI.SidorenkoCounterexample.ProofCertificate_0194 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0194 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7

omit [FiniteDimensional K E] in
theorem certificate_proof_0195 (B : LinearMap.BilinForm K E) :
    Nat.card (E ≃ₗ[K] E) ≤ Nat.card (FormOrbit B) * Nat.card (BilinAut B) :=
  card_le_card_mul_of_fibers (formOrbitMap B) _ (formOrbit_fiber_bound B)

private instance certificate_instance_0195 : OAI.SidorenkoCounterexample.ProofCertificate_0195 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0195 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0196 : Fintype.card K ^ (finrank K E * finrank K E) ≤
    2 ^ finrank K E * Nat.card (E ≃ₗ[K] E) := by
  rw [linearAut_card]
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hfac (i : Fin (finrank K E)) : Fintype.card K ^ finrank K E ≤
      2 * (Fintype.card K ^ finrank K E - Fintype.card K ^ i.val) := by
    have hle : Fintype.card K ^ (i.val+1) ≤ Fintype.card K ^ finrank K E :=
      Nat.pow_le_pow_right (by omega) i.isLt
    have hh : 2 * Fintype.card K ^ i.val ≤ Fintype.card K ^ finrank K E := by
      calc
        _ ≤ Fintype.card K * Fintype.card K ^ i.val := Nat.mul_le_mul_right _ hq
        _ = Fintype.card K ^ (i.val+1) := by rw [pow_succ]; ring
        _ ≤ _ := hle
    omega
  calc
    _ = ∏ _i : Fin (finrank K E), Fintype.card K ^ finrank K E := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul]
    _ ≤ ∏ i : Fin (finrank K E), 2 * (Fintype.card K ^ finrank K E - Fintype.card K ^ i.val) :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hfac i)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

private instance certificate_instance_0196 : OAI.SidorenkoCounterexample.ProofCertificate_0196 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0196 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7

variable [Invertible (2 : K)]
theorem certificate_proof_0197 (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (hB : B.Nondegenerate) :
    Fintype.card K ^ (finrank K E+1).choose 2 ≤
      4 ^ finrank K E * Nat.card (FormOrbit B) := by
  let d := finrank K E
  let q := Fintype.card K
  have h1 := (linearAut_card_lower (K := K) (E := E)).trans
    (Nat.mul_le_mul_left (2^d) (formOrbit_card_mul_bound B))
  have h2 := Nat.mul_le_mul_left (2^d * Nat.card (FormOrbit B)) (bilinAut_card_bound B hs hB)
  have hh : q^(d*d) ≤ (4^d * Nat.card (FormOrbit B)) * q^d.choose 2 := by
    calc
      _ ≤ 2^d * (Nat.card (FormOrbit B) * Nat.card (BilinAut B)) := h1
      _ = (2^d * Nat.card (FormOrbit B)) * Nat.card (BilinAut B) := by ring
      _ ≤ (2^d * Nat.card (FormOrbit B)) * (2^d * q^d.choose 2) := h2
      _ = _ := by rw [show (4 : ℕ) = 2*2 from rfl,mul_pow]; ring
  have hd : d*d = (d+1).choose 2 + d.choose 2 := by
    have hc : ∀ n : ℕ, n*n = n + 2*n.choose 2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith
    rw [Nat.choose_succ_succ,Nat.choose_one_right]
    linear_combination hc d
  rw [hd,pow_add] at hh
  exact Nat.le_of_mul_le_mul_right hh (pow_pos Fintype.card_pos _)

private instance certificate_instance_0197 : OAI.SidorenkoCounterexample.ProofCertificate_0197 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0197 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end FormOrbits
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TransverseForms
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
theorem certificate_proof_0198 (B : LinearMap.BilinForm K V) (hs : B.IsSymm) :
    canonicalSymplectic.orthogonal B.graph = B.graph := by
  ext x
  constructor
  · intro hx
    apply (B.mem_graph_iff x).mpr
    ext y
    have hh := hx (y,B y) (by rfl)
    change x.2 y - B y x.1 = 0 at hh
    exact (sub_eq_zero.mp hh).trans (hs.eq y x.1)
  · intro hx y hy
    have hx' := (B.mem_graph_iff x).mp hx
    have hy' := (B.mem_graph_iff y).mp hy
    change x.2 y.1 - y.2 x.1 = 0
    rw [hx',hy',hs.eq]
    exact sub_self _

private instance certificate_instance_0198 : OAI.SidorenkoCounterexample.ProofCertificate_0198 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0198 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0199 : Function.Injective
    (fun B : LinearMap.BilinForm K V => B.graph) := by
  intro B C h
  change B.graph = C.graph at h
  apply LinearMap.ext
  intro x
  have hx : (x,B x) ∈ C.graph := by rw [← h]; rfl
  exact (C.mem_graph_iff _).mp hx

private instance certificate_instance_0199 : OAI.SidorenkoCounterexample.ProofCertificate_0199 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0199 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4

theorem certificate_proof_0200 (g : V ≃ₗ[K] V) (x y : V × Module.Dual K V) :
    canonicalSymplectic (formCoordinateEquiv g x) (formCoordinateEquiv g y) =
      canonicalSymplectic x y := by
  simp [formCoordinateEquiv,canonicalSymplectic_apply]

private instance certificate_instance_0200 : OAI.SidorenkoCounterexample.ProofCertificate_0200 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0200 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0201 (B : LinearMap.BilinForm K V) (g : V ≃ₗ[K] V) :
    B.graph.map (formCoordinateEquiv g).toLinearMap = (B.comp g.toLinearMap g.toLinearMap).graph := by
  apply subspace_map_eq_of_mem_iff
  intro x
  change g.dualMap x.2 = (B.comp g.toLinearMap g.toLinearMap) (g.symm x.1) ↔ x.2 = B x.1
  constructor
  · intro h
    ext y
    have hh := LinearMap.congr_fun h (g.symm y)
    simpa [LinearEquiv.dualMap_apply,LinearMap.BilinForm.comp_apply] using hh
  · intro h
    ext y
    simp [LinearEquiv.dualMap_apply,LinearMap.BilinForm.comp_apply,h]

private instance certificate_instance_0201 : OAI.SidorenkoCounterexample.ProofCertificate_0201 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0201 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6

end TransverseForms
section TransverseTripleCoordinates
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0202 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : Submodule K E) (hL : ω.orthogonal L = L)
    (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥) :
    ∃ (e : (L × Module.Dual K L) ≃ₗ[K] E) (B : LinearMap.BilinForm K L),
      B.IsSymm ∧ B.Nondegenerate ∧
      (∀ x, e x ∈ L ↔ x.2 = 0) ∧ (∀ x, e x ∈ M ↔ x.1 = 0) ∧
      (∀ x, e x ∈ N ↔ x.2 = B x.1) ∧
      (∀ x y, ω (e x) (e y) = canonicalSymplectic x y) := by
  obtain ⟨e,heL,heM,heform⟩ := exists_transverse_pair_coordinates ω ha hω L M hL hM hLM
  let p : N →ₗ[K] L := (LinearMap.fst K L (Module.Dual K L)).comp
    (e.symm.toLinearMap.comp N.subtype)
  have hp : Function.Injective p := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro n hn
    have hm : n.val ∈ M := by
      have hh : e (e.symm n.val) ∈ M := (heM _).mpr hn
      simpa only [e.apply_symm_apply] using hh
    have hz : n.val ∈ M ⊓ N := ⟨hm,n.property⟩
    apply Subtype.ext
    change n.val = 0
    simpa only [hMN,Submodule.mem_bot] using hz
  have hd : finrank K N = finrank K L := by
    have h1 := self_orthogonal_twice_finrank ω N hω hN
    have h2 := self_orthogonal_twice_finrank ω L hω hL
    omega
  let a : N ≃ₗ[K] L := LinearEquiv.ofBijective p
    ⟨hp,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hp⟩
  let B : LinearMap.BilinForm K L := (LinearMap.snd K L (Module.Dual K L)).comp
    (e.symm.toLinearMap.comp (N.subtype.comp a.symm.toLinearMap))
  have hcoord (x : L) : e.symm (a.symm x).val = (x,B x) := by
    apply Prod.ext
    · exact a.apply_symm_apply x
    · rfl
  have hNgraph (x : L × Module.Dual K L) : e x ∈ N ↔ x.2 = B x.1 := by
    constructor
    · intro hx
      let n : N := ⟨e x,hx⟩
      have haN : a n = x.1 := by
        change (e.symm (e x)).1 = x.1
        rw [e.symm_apply_apply]
      have hh := hcoord (a n)
      rw [a.symm_apply_apply,haN] at hh
      have hh' := congrArg Prod.snd hh
      change (e.symm (e x)).2 = B x.1 at hh'
      simpa only [e.symm_apply_apply] using hh'
    · intro hx
      have hh := congrArg e (hcoord x.1)
      rw [e.apply_symm_apply,← hx] at hh
      exact hh ▸ (a.symm x.1).property
  have hs : B.IsSymm := by
    constructor
    intro x y
    have hh := hN.ge ((a.symm y).property) (a.symm x).val ((a.symm x).property)
    rw [← e.apply_symm_apply (a.symm x).val,← e.apply_symm_apply (a.symm y).val,
      heform,hcoord,hcoord] at hh
    change B y x - B x y = 0 at hh
    exact (sub_eq_zero.mp hh).symm
  have hleft (x : L) (hx : ∀ y, B x y = 0) : x = 0 := by
    have hxB : B x = 0 := by ext y; exact hx y
    have hxL : (a.symm x).val ∈ L := by
      have hh := (heL (x,B x)).mpr hxB
      have hc := congrArg e (hcoord x)
      rw [e.apply_symm_apply] at hc
      exact hc.symm ▸ hh
    have hz : (a.symm x).val ∈ L ⊓ N := ⟨hxL,(a.symm x).property⟩
    have hn0 : a.symm x = 0 := Subtype.ext (by
      change (a.symm x).val = 0
      simpa only [hLN,Submodule.mem_bot] using hz)
    have hh := congrArg a hn0
    simpa only [a.apply_symm_apply,map_zero] using hh
  refine ⟨e,B,hs,⟨hleft,?_⟩,heL,heM,hNgraph,heform⟩
  intro x hx
  exact hleft x (fun y => (hs.eq x y).trans (hx y))

private instance certificate_instance_0202 : OAI.SidorenkoCounterexample.ProofCertificate_0202 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0202 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

end TransverseTripleCoordinates
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FixedPairOrbit
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : Submodule K E)
theorem certificate_proof_0203 (hN : ω.orthogonal N = N)
    (N' : FixedPairOrbit ω L M N) : ω.orthogonal N'.val = N'.val := by
  obtain ⟨e,he,_,_,hne⟩ := N'.property
  rw [←hne,orthogonal_map_of_isometry ω e he,hN]

private instance certificate_instance_0203 : OAI.SidorenkoCounterexample.ProofCertificate_0203 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0203 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

variable [FiniteDimensional K E]
theorem certificate_proof_0204 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥) :
    ∃ B : LinearMap.BilinForm K L, B.IsSymm ∧ B.Nondegenerate ∧
      ∃ f : FormOrbit B → FixedPairOrbit ω L M N, Function.Injective f := by
  classical
  obtain ⟨e,B,hs,hB,heL,heM,heN,heform⟩ :=
    exists_transverse_triple_form ω ha hω L M N hL hM hN hLM hLN hMN
  have hgood (C : FormOrbit B) :
      ∃ f : E ≃ₗ[K] E, (∀ x y, ω (f x) (f y) = ω x y) ∧
        L.map f.toLinearMap = L ∧ M.map f.toLinearMap = M ∧
        N.map f.toLinearMap = C.val.graph.map e.toLinearMap := by
    obtain ⟨g,hg⟩ := C.property
    let f := e.symm.trans ((formCoordinateEquiv g).trans e)
    refine ⟨f,?_,?_,?_,?_⟩
    · intro x y
      change ω (e (formCoordinateEquiv g (e.symm x)))
        (e (formCoordinateEquiv g (e.symm y)))=ω x y
      rw [heform,formCoordinateEquiv_isometry,←heform,e.apply_symm_apply,e.apply_symm_apply]
    · apply subspace_map_eq_of_mem_iff f
      intro x
      change e (formCoordinateEquiv g (e.symm x)) ∈ L ↔ x ∈ L
      rw [heL]
      change g.dualMap (e.symm x).2 = 0 ↔ x ∈ L
      rw [LinearEquiv.map_eq_zero_iff]
      simpa only [e.apply_symm_apply] using (heL (e.symm x)).symm
    · apply subspace_map_eq_of_mem_iff f
      intro x
      change e (formCoordinateEquiv g (e.symm x)) ∈ M ↔ x ∈ M
      rw [heM]
      change g.symm (e.symm x).1 = 0 ↔ x ∈ M
      rw [LinearEquiv.map_eq_zero_iff]
      simpa only [e.apply_symm_apply] using (heM (e.symm x)).symm
    · apply subspace_map_eq_of_mem_iff f
      intro x
      rw [Submodule.mem_map_equiv]
      change e.symm (e (formCoordinateEquiv g (e.symm x))) ∈ C.val.graph ↔ x ∈ N
      rw [e.symm_apply_apply,hg,←fullGraph_congruence,Submodule.mem_map_equiv]
      rw [LinearEquiv.symm_apply_apply,LinearMap.mem_graph_iff]
      simpa only [e.apply_symm_apply] using (heN (e.symm x)).symm
  let f : FormOrbit B → FixedPairOrbit ω L M N :=
    fun C => ⟨C.val.graph.map e.toLinearMap,hgood C⟩
  refine ⟨B,hs,hB,f,?_⟩
  intro C D h
  apply Subtype.ext
  apply fullGraph_injective
  exact Submodule.map_injective_of_injective e.injective (congrArg Subtype.val h)

private instance certificate_instance_0204 : OAI.SidorenkoCounterexample.ProofCertificate_0204 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0204 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

variable [Fintype K] [Finite E] [Invertible (2 : K)]
theorem certificate_proof_0205 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥) :
    Fintype.card K ^ (finrank K L+1).choose 2 ≤
      4 ^ finrank K L * Nat.card (FixedPairOrbit ω L M N) := by
  obtain ⟨B,hs,hB,f,hf⟩ := fixedPairOrbit_form_injection ω L M N ha hω hL hM hN hLM hLN hMN
  exact (formOrbit_card_lower B hs hB).trans
    (Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective f hf))

private instance certificate_instance_0205 : OAI.SidorenkoCounterexample.ProofCertificate_0205 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
  exact @certificate_proof_0205 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20

end FixedPairOrbit
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section UniformCountingBounds
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]
theorem certificate_proof_0206 :
    Nat.card (Lagrangian (K := K) (V := V)) =
      ∑ k : Fin (finrank K V+1), Nat.card (DimSubspace K V k.val) *
        Fintype.card K ^ (k.val+1).choose 2 := by
  classical
  let := Fintype.ofFinite (Submodule K V)
  let d : Submodule K V → Fin (finrank K V+1) :=
    fun U => ⟨finrank K U,Nat.lt_succ_of_le (Submodule.finrank_le U)⟩
  rw [lagrangian_card_sum]
  classical
  have hs := Fintype.sum_fiberwise d (fun U : Submodule K V => Fintype.card K ^ (finrank K U+1).choose 2)
  convert hs.symm.trans ?_ using 1 <;> try { congr 2; exact Subsingleton.elim _ _ }
  apply Finset.sum_congr rfl
  intro k _
  have hc : Nat.card {U : Submodule K V // d U = k} = Nat.card (DimSubspace K V k.val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun U => by
      change (⟨finrank K U,_⟩ : Fin _)=k ↔ finrank K U=k.val
      exact Fin.ext_iff))
  have he (U : {U : Submodule K V // d U = k}) : finrank K U.val = k.val :=
    congrArg Fin.val U.property
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card,hc,Nat.cast_id]

private instance certificate_instance_0206 : OAI.SidorenkoCounterexample.ProofCertificate_0206 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0206 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0207 (n : ℕ) : 0 < lagrangianConstant n := by
  unfold lagrangianConstant
  positivity

private instance certificate_instance_0207 : OAI.SidorenkoCounterexample.ProofCertificate_0207 := by
  constructor
  intro q0
  exact @certificate_proof_0207 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0

theorem certificate_proof_0208 :
    (Nat.card (Lagrangian (K := K) (V := V)) : ℝ) ≤
      lagrangianConstant (finrank K V) * (Fintype.card K : ℝ)^((finrank K V+1).choose 2) := by
  rw [lagrangian_card_by_dimension,Nat.cast_sum]
  let n := finrank K V
  let q : ℝ := Fintype.card K
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos (α := K)))
  have hterm (k : Fin (n+1)) :
      (Nat.card (DimSubspace K V k.val) : ℝ) * q^(k.val+1).choose 2 ≤
        2^n*q^(n+1).choose 2 := by
    have hk : k.val ≤ n := Nat.le_of_lt_succ k.isLt
    have he : k.val*(n-k.val)+(k.val+1).choose 2 ≤ (n+1).choose 2 := by
      have hh := symmetric_nullity_exponent n (n-k.val) (Nat.sub_le n k.val)
      rw [Nat.sub_sub_self hk] at hh
      nlinarith
    calc
      _ ≤ (2^k.val*q^(k.val*(n-k.val)))*q^(k.val+1).choose 2 :=
        mul_le_mul_of_nonneg_right (subspace_count_upper k.val hk) (by positivity)
      _ = 2^k.val*q^(k.val*(n-k.val)+(k.val+1).choose 2) := by rw [pow_add]; ring
      _ ≤ 2^n*q^(n+1).choose 2 := mul_le_mul
        (pow_le_pow_right₀ (by norm_num) hk) (pow_le_pow_right₀ hq he) (by positivity) (by positivity)
  calc
    _ ≤ ∑ _k : Fin (n+1), 2^n*q^(n+1).choose 2 := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [Nat.cast_mul,Nat.cast_pow] using hterm k
    _ = _ := by simp [lagrangianConstant,n,q]; ring

private instance certificate_instance_0208 : OAI.SidorenkoCounterexample.ProofCertificate_0208 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0208 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0209 :
    (Fintype.card K : ℝ)^((finrank K V+1).choose 2) ≤
      Nat.card (Lagrangian (K := K) (V := V)) := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  have h := Nat.card_le_card_of_injective (graphLagrangian (K := K) (V := V) (⊤ : Submodule K V))
    (graphLagrangian_form_injective (⊤ : Submodule K V))
  rw [symForm_card] at h
  simpa only [finrank_top,Nat.cast_pow] using (show
    ((Fintype.card K^((finrank K ↥(⊤ : Submodule K V)+1).choose 2) : ℕ) : ℝ) ≤
      (Nat.card (Lagrangian (K := K) (V := V)) : ℝ) from by exact_mod_cast h)

private instance certificate_instance_0209 : OAI.SidorenkoCounterexample.ProofCertificate_0209 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0209 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 q0 q1 q2 q3 q4 q5 q6

end UniformCountingBounds
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullTripleOrbit
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [FiniteDimensional K E]
end FullTripleOrbit
section CanonicalTripleMass
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]
local notation "ω" => (canonicalSymplectic (K := K) (V := V))
end CanonicalTripleMass
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0182 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0183 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0184 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0185 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0186 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0187 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0188 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0189 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0190 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0191 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0192 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0193 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0194 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0195 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0196 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0197 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0198 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0199 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0200 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0201 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0202 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0203 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0204 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0205 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0206 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0207 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0208 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0209 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

