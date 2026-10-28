-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.dihedral_entry_pairing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:59:09.010672+00:00
-- url     : https://prove2.me/submissions/a6d76db4-36eb-4cb7-8bdc-ae94a8cca321

import Mathlib
import Definitions.Def_OAIQ039C059
import Theorems.Thm_OAI_Kadison_DihedralCorner_compression_rotation_sandwich
import Theorems.Thm_OAI_Kadison_DihedralCorner_compression_symmetry_sandwich

section
-- module Solutions.OAIQ039_CM.Commutator_DihedralHaar
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} (τ : A →ₗ[ℂ] ℂ)

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
  (hstar : ∀ a : A, τ (star a)=star (τ a)) (hfree : Free S τ)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d : A)∈S i) (hs : (s : A)∈S j)
  (hd0 : τ (d : A)=0) (hs0 : τ (s : A)=0)

lemma wave_nat (u : unitary A) (n : ℕ) : wave u (n:ℤ)=(u:A)^n := by
  simp only [wave,zpow_natCast,SubmonoidClass.coe_pow]

lemma symmetry_star (u : unitary A) (hu : (u:A)*(u:A)=1) : star (u:A)=(u:A) := by
  have h := congrArg ((star (u:A)) * ·) hu
  simpa only [←mul_assoc,Unitary.coe_star_mul_self,one_mul,mul_one] using h.symm

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SubfactorExpectation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} {S T : ι → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

variable (hsub : ∀ i, T i≤S i)

lemma Reduced.enlarge {w : List (Letter T τ)} (hw : Reduced w) :
    Reduced (w.map (Letter.enlarge hsub)) := by
  exact (List.isChain_map (Letter.enlarge hsub)).mpr hw

variable (hstar : ∀ a : A, τ (star a)=star (τ a)) (h1 : τ 1=1) (hfree : Free S τ)

include hsub hstar h1 hfree in
lemma residual_word_pairing {j : ι} {a : A} (ha : a∈S j) (ha0 : τ a=0)
    (haT : ∀ b∈T j, τ (a*b)=0) (w : List (Letter T τ)) (hw : Reduced w) :
    τ (a*word w)=0 := by
  let b : Letter S τ := ⟨j,star a,star_mem ha,by rw [hstar,ha0,star_zero]⟩
  have hg := gram_word hstar h1 hfree [b] (w.map (Letter.enlarge hsub))
    (reduced_singleton b) (hw.enlarge hsub)
  simp only [word_enlarge,word_cons,word_nil,mul_one,b,star_star] at hg
  change τ (a*word w)=gram [b] (w.map (Letter.enlarge hsub)) at hg
  rw [hg]
  cases w with
  | nil => rfl
  | cons c w =>
    cases w with
    | nil =>
      by_cases hj : j=c.color
      · simp only [List.map_cons,List.map_nil,gram,b,Letter.enlarge,ite_eq_left hj,
          star_star,mul_one]
        exact haT c.val (hj ▸ c.mem)
      · simp [gram,b,Letter.enlarge,hj]
    | cons c' w =>
      simp only [List.map_cons,gram,b,Letter.enlarge,star_star]
      split_ifs <;> simp

include hsub hstar h1 hfree in
lemma residual_generated_pairing {j : ι} {a x : A} (ha : a∈S j) (ha0 : τ a=0)
    (haT : ∀ b∈T j, τ (a*b)=0) (hx : x∈⨆ i,T i) : τ (a*x)=0 := by
  rw [←reducedAlgebra_eq_iSup (S := T) hstar h1] at hx
  change x∈wordSpan T τ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,hw,rfl⟩ := hx
    exact residual_word_pairing hsub hstar h1 hfree ha ha0 haT w hw
  | zero => simp
  | add x y _ _ hx hy => simp only [mul_add,map_add,hx,hy,add_zero]
  | smul z x _ hx => simp only [mul_smul_comm,map_smul,hx,smul_zero]

end Kadison.FreeMoments

namespace Kadison.SymmetryAlgebra

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable (s : A) (hs : star s=s) (hs2 : s*s=1)

lemma self_mem : s∈algebra s hs hs2 := ⟨0,1,by simp⟩

lemma le_factor (D : StarSubalgebra ℂ A) (h : s∈D) : algebra s hs hs2≤D := by
  rintro a ⟨z,w,rfl⟩
  exact D.add_mem (D.smul_mem D.one_mem z) (D.smul_mem h w)

variable (S : Bool → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

variable (hsS : s∈S true) (hs0 : τ s=0) (hstar : ∀ a : A, τ (star a)=star (τ a))
  (h1 : τ 1=1) (hfree : FreeMoments.Free S τ)

include hsS in
lemma factors_le (i : Bool) : factors s hs hs2 S i≤S i := by
  cases i
  · exact le_rfl
  · exact le_factor s hs hs2 (S true) hsS

include hsS hs0 hstar h1 hfree in
theorem pairing_projection {a x : A} (ha : a∈S true)
    (hx : x∈⨆ i,factors s hs hs2 S i) :
    τ (a*x)=τ a*τ x+τ (a*s)*τ (s*x) := by
  let r := a-τ a • (1:A)-τ (a*s) • s
  have hr : r∈S true := (S true).sub_mem
    ((S true).sub_mem ha ((S true).smul_mem (S true).one_mem _)) ((S true).smul_mem hsS _)
  have hr0 : τ r=0 := by simp [r,map_sub,map_smul,h1,hs0]
  have hrs : τ (r*s)=0 := by
    simp [r,sub_mul,map_sub,map_smul,hs2,h1,hs0]
  have hrT : ∀ b∈factors s hs hs2 S true, τ (r*b)=0 := by
    rintro b ⟨z,w,rfl⟩
    simp only [mul_add,mul_smul_comm,mul_one,map_add,map_smul,hr0,hrs,smul_zero,add_zero]
  have hz := FreeMoments.residual_generated_pairing
    (factors_le s hs hs2 S hsS) hstar h1 hfree hr hr0 hrT hx
  dsimp only [r] at hz
  simp only [sub_mul,smul_mul_assoc,one_mul,map_sub,map_smul,smul_eq_mul] at hz
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hz)).trans (add_comm _ _)

end Kadison.SymmetryAlgebra

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DihedralExpectationEntries
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

lemma wave_mem (R : StarSubalgebra ℂ A) (u : unitary A) (hu : (u:A)∈R)
    (n : ℤ) : wave u n∈R := by
  cases n with
  | ofNat n =>
    change wave u (n:ℤ)∈R
    rw [wave_nat]
    exact R.pow_mem hu n
  | negSucc n =>
    change wave u (-((n+1:ℕ):ℤ))∈R
    rw [←wave_star,wave_nat]
    exact star_mem (R.pow_mem hu _)

lemma cosineAlgebra_coe_mem (R : StarSubalgebra ℂ A) (u d : unitary A)
    (hr : MulAut.conj d u=u⁻¹) {p : A} (hp : IsStarProjection p)
    (hpform : p=(1/2:ℂ) • (1+(d:A))) (hdp : (d:A)*p=p)
    (hpR : p∈R) (huR : (u:A)∈R) {b : Corner hp}
    (hb : b∈cosineAlgebra u d hr hp hpform hdp) : (b:A)∈R := by
  change b∈cosineSpace u hp at hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨n,rfl⟩ := hb
    exact R.mul_mem (R.mul_mem hpR (wave_mem R u huR n)) hpR
  | zero => exact R.zero_mem
  | add b c _ _ hb hc => exact R.add_mem hb hc
  | smul z b _ hb => exact R.smul_mem hb z

variable (S : Bool → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
  (hstar : ∀ a : A, τ (star a)=star (τ a)) (hfree : Free S τ)

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : τ (d:A)=0) (hs0 : τ (s:A)=0)

variable (hr : MulAut.conj d (d*s)=(d*s)⁻¹) (hd2 : (d:A)*(d:A)=1)
  (hs2 : (s:A)*(s:A)=1)

variable {p : A} (hp : IsStarProjection p) (hpform : p=(1/2:ℂ) • (1+(d:A)))
  (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)

include h1 htr hstar hfree hd hs hd0 hs0 hd2 hpd hs2 in
theorem compression_expectation_pairing (hpD : p∈S false) (e b : Corner hp)
    (he : e∈cornerFactor hp (S false) hpD)
    (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
    (hb0 : halfCornerTrace hp τ b=0) {a : A} (ha : a∈S true) (j k : ℤ) :
    τ (a*(wave (d*s) j*((e:A)*(b:A)*(e:A))*wave (d*s) (-k)))=
      τ a*(halfCornerTrace hp τ e)^2*τ (wave (d*s) (j-k)*(b:A))+
      τ (a*(s:A))*(halfCornerTrace hp τ e)^2*τ (wave (d*s) (j+k+1)*(b:A)) := by
  let R := ⨆ i,SymmetryAlgebra.factors (s:A) (symmetry_star s hs2) hs2 S i
  have hDR : S false≤R := le_iSup (fun i => SymmetryAlgebra.factors
    (s:A) (symmetry_star s hs2) hs2 S i) false
  have hsR : (s:A)∈R := (le_iSup (fun i => SymmetryAlgebra.factors
    (s:A) (symmetry_star s hs2) hs2 S i) true) (SymmetryAlgebra.self_mem (s:A) (symmetry_star s hs2) hs2)
  have hwR : ((d*s:unitary A):A)∈R := R.mul_mem (hDR hd) hsR
  have heR : (e:A)∈R := hDR he
  have hbR := cosineAlgebra_coe_mem R (d*s) d hr hp hpform hdp (hDR hpD) hwR hb
  have hx : wave (d*s) j*((e:A)*(b:A)*(e:A))*wave (d*s) (-k)∈R :=
    R.mul_mem (R.mul_mem (wave_mem R _ hwR _) (R.mul_mem (R.mul_mem heR hbR) heR))
      (wave_mem R _ hwR _)
  rw [SymmetryAlgebra.pairing_projection (s:A) (symmetry_star s hs2) hs2 S τ
      hs hs0 hstar h1 hfree ha hx,
    compression_rotation_sandwich τ h1 htr hstar hfree d s false true Bool.false_ne_true
      hd hs hd0 hs0 hr hd2 hp hpform hpd hdp hpD e b he hb hb0,
    compression_symmetry_sandwich τ h1 htr hstar hfree d s false true Bool.false_ne_true
      hd hs hd0 hs0 hr hd2 hp hpform hpd hdp hpD e b he hb hb0]
  ring

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeHilbertEntries
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

lemma baseEmbedding_coe (v : factorSpace t S true) :
    baseEmbedding t S hfree (v : multiplicityLevel t S true 0)=
      (t.functional.toPreGNS (factorValue t S true v) : t.functional.GNS) := by
  simp [baseEmbedding,blockEmbedding,blockIsometry,blockReadPre,blockRead]

lemma inner_gns_coe (a b : A) :
    inner ℂ (t.functional.toPreGNS a : t.functional.GNS)
      (t.functional.toPreGNS b : t.functional.GNS)=t.functional (star a*b) := by
  rw [Completion.inner_coe]
  rfl

lemma baseAction_inner (a : A) (v z : factorSpace t S true) :
    inner ℂ (z : multiplicityLevel t S true 0)
      (baseAction t S hfree a (v : multiplicityLevel t S true 0))=
      t.functional (star (factorValue t S true z)*a*factorValue t S true v) := by
  dsimp only [baseAction,ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right
    (E := multiplicityLevel t S true 0) (F := t.functional.GNS)]
  change inner ℂ (baseEmbedding t S hfree (z : multiplicityLevel t S true 0))
    (t.functional.gnsStarAlgHom a
      (baseEmbedding t S hfree (v : multiplicityLevel t S true 0)))=_
  rw [baseEmbedding_coe,baseEmbedding_coe,TracialGNS.left_coe,inner_gns_coe,mul_assoc]

lemma base_inner (v z : factorSpace t S true) :
    inner ℂ (z : multiplicityLevel t S true 0) (v : multiplicityLevel t S true 0)=
      t.functional (star (factorValue t S true z)*factorValue t S true v) := by
  rw [Completion.inner_coe]
  rfl

lemma dihedralColumn_coe (e : A) (w : unitary A) (c : ℝ) (n : ℕ)
    (v : factorSpace t S true) :
    dihedralColumn t S hfree e w c n (v : multiplicityLevel t S true 0)=
      (c:ℂ) • (t.functional.toPreGNS
        (e*DihedralCorner.wave w (-(n:ℤ))*factorValue t S true v) : t.functional.GNS) := by
  change (c:ℂ) • t.functional.gnsStarAlgHom _
    (baseEmbedding t S hfree (v : multiplicityLevel t S true 0))=_
  rw [baseEmbedding_coe,TracialGNS.left_coe]

lemma dihedralColumn_inner (e h : A) (he : IsStarProjection e) (heh : e*h*e=h)
    (w : unitary A) (c : ℝ) (n m : ℕ) (v z : factorSpace t S true) :
    inner ℂ (dihedralColumn t S hfree e w c n (z : multiplicityLevel t S true 0))
      (t.functional.gnsStarAlgHom h
        (dihedralColumn t S hfree e w c m (v : multiplicityLevel t S true 0)))=
    ((c:ℂ)^2)*t.functional (star (factorValue t S true z)*
      (DihedralCorner.wave w (n:ℤ)*h*DihedralCorner.wave w (-(m:ℤ)))*
      factorValue t S true v) := by
  rw [dihedralColumn_coe,dihedralColumn_coe,map_smul,inner_smul_left,inner_smul_right,
    TracialGNS.left_coe,inner_gns_coe]
  rw [star_mul,star_mul,he.isSelfAdjoint.star_eq,DihedralCorner.wave_star,neg_neg]
  rw [show (starRingEnd ℂ) (c:ℂ)=(c:ℂ) from Complex.conj_ofReal c]
  change (c:ℂ)*((c:ℂ)*t.functional
    (star (factorValue t S true z)*(DihedralCorner.wave w (n:ℤ)*e)*
      (h*(e*DihedralCorner.wave w (-(m:ℤ))*factorValue t S true v))))=_
  rw [←mul_assoc (star (factorValue t S true z))]
  have hm : star (factorValue t S true z)*DihedralCorner.wave w (n:ℤ)*e*
      (h*(e*DihedralCorner.wave w (-(m:ℤ))*factorValue t S true v))=
      star (factorValue t S true z)*
        (DihedralCorner.wave w (n:ℤ)*h*DihedralCorner.wave w (-(m:ℤ)))*
        factorValue t S true v := by
    calc
      _ = star (factorValue t S true z)*
        (DihedralCorner.wave w (n:ℤ)*(e*h*e)*DihedralCorner.wave w (-(m:ℤ)))*
        factorValue t S true v := by simp only [mul_assoc]
      _ = _ := by rw [heh]
  rw [hm,pow_two]
  ring

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeDihedralEntries
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hr : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

variable (e b : Corner hp) (he : e∈cornerFactor hp (S false) hpD)
  (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
  (hb0 : halfCornerTrace hp t.functional.toLinearMap b=0)

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_projection_coe (heproj : IsStarProjection e) : IsStarProjection (e:A) where
  isSelfAdjoint := by
    show star (e:A)=(e:A)
    exact congrArg (fun a : Corner hp => (a:A)) heproj.isSelfAdjoint.star_eq
  isIdempotentElem := by
    show (e:A)*(e:A)=(e:A)
    exact congrArg (fun a : Corner hp => (a:A)) heproj.isIdempotentElem.eq

omit [PartialOrder A] [StarOrderedRing A] in
lemma sandwich_supported (heproj : IsStarProjection e) :
    (e:A)*((e:A)*(b:A)*(e:A))*(e:A)=(e:A)*(b:A)*(e:A) := by
  have h := (corner_projection_coe hp (e := e) heproj).isIdempotentElem.eq
  calc
    _ = ((e:A)*(e:A))*(b:A)*((e:A)*(e:A)) := by simp only [mul_assoc]
    _ = _ := by rw [h]

include htr hd hs hd0 hs0 hd2 hs2 hpd he hb hb0 in
theorem dihedral_entry_pairing_oai (heproj : IsStarProjection e)
    (c : ℝ) (n m : ℕ) (v z : factorSpace t S true) :
    inner ℂ (dihedralColumn t S hfree (e:A) (d*s) c n (z : multiplicityLevel t S true 0))
      (t.functional.gnsStarAlgHom ((e:A)*(b:A)*(e:A))
        (dihedralColumn t S hfree (e:A) (d*s) c m (v : multiplicityLevel t S true 0)))=
    ((c:ℂ)^2*(halfCornerTrace hp t.functional.toLinearMap e)^2)*
      (t.functional (wave (d*s) ((n:ℤ)-m)*(b:A))*
        inner ℂ (z : multiplicityLevel t S true 0) (v : multiplicityLevel t S true 0)+
       t.functional (wave (d*s) ((n:ℤ)+m+1)*(b:A))*
        inner ℂ (z : multiplicityLevel t S true 0)
          (baseAction t S hfree (s:A) (v : multiplicityLevel t S true 0))) := by
  rw [dihedralColumn_inner t S hfree (e:A) _ (corner_projection_coe hp (e := e) heproj)
    (sandwich_supported hp (e := e) (b := b) heproj),base_inner,baseAction_inner]
  have hv : factorValue t S true v∈S true := by exact v.property
  have hz : factorValue t S true z∈S true := by exact z.property
  have hh := compression_expectation_pairing S t.functional.toLinearMap t.normalized htr
    (fun a => map_star t.functional a) hfree d s hd hs hd0 hs0 hr hd2 hs2
    hp hpform hpd hdp hpD e b he hb hb0 ((S true).mul_mem hv ((S true).star_mem' hz))
    (n:ℤ) (m:ℤ)
  have hrot : t.functional (star (factorValue t S true z)*
      (wave (d*s) (n:ℤ)*((e:A)*(b:A)*(e:A))*wave (d*s) (-(m:ℤ)))*
      factorValue t S true v)=
    t.functional ((factorValue t S true v*star (factorValue t S true z))*
      (wave (d*s) (n:ℤ)*((e:A)*(b:A)*(e:A))*wave (d*s) (-(m:ℤ)))) := by
    rw [htr]
    congr 1
    exact mul_assoc _ _ _ |>.symm
  rw [hrot]
  change (c:ℂ)^2*t.functional.toLinearMap _=_
  rw [hh]
  have hrot0 := htr (factorValue t S true v) (star (factorValue t S true z))
  have hrot1 : t.functional (factorValue t S true v*star (factorValue t S true z)*(s:A))=
      t.functional (star (factorValue t S true z)*(s:A)*factorValue t S true v) := by
    rw [mul_assoc,htr]
  change (c:ℂ)^2*(t.functional _*_ * t.functional _ +t.functional _*_ * t.functional _)=_
  rw [hrot0,hrot1]
  ring

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.FreeBlocks.dihedral_entry_pairing_oai := @OAI.Kadison.FreeBlocks.dihedral_entry_pairing_oai
