-- Prove2me | solution 1 for OAI.ElasticityAugmented.restricted_transports_of_chart_equal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:28:03.808045+00:00
-- url     : https://prove2.me/submissions/c46807d5-a363-46fc-a03f-59ff905dc366

import Mathlib
import Definitions.Def_OAIQ6El006

section
-- module Solutions.OAIQ6_Elast.Elasticity_Augmented
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact differential-algebra identities of the physical and normalized
augmented elasticity systems. Smooth derivatives are constructed below;
commutation and Leibniz are proved, not postulated for the physical operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

section DifferentialAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A)

omit [Fintype ι] in
lemma partial_mul (i : ι) (a b : A) : D i (a*b) = D i a*b + a*D i b := by
  simpa only [smul_eq_mul, add_comm, mul_comm] using (D i).leibniz a b

end DifferentialAlgebra

end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_PhysicalCGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityAugmented

section
open scoped BigOperators

lemma coord_ofReal (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) (x : X) :
    (coord i (smoothOfReal f hf) : X → ℂ) x=(fderiv ℝ f x (e i) : ℂ) := by
  have hh := Complex.ofRealCLM.hasFDerivAt.comp x ((hf.differentiable (by simp)) x).hasFDerivAt
  exact congrArg (fun L : X →L[ℝ] ℂ => L (e i)) hh.fderiv
lemma recovery_basis (i : Fin 3) : ElasticityRecovery.basis i=e i := by
  simp [ElasticityRecovery.basis,e,EuclideanSpace.basisFun_apply]
lemma coord_ofReal_grad (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) (x : X) :
    (coord i (smoothOfReal f hf) : X → ℂ) x=(ElasticityRecovery.grad f x i : ℂ) := by
  rw [coord_ofReal]
  simp only [ElasticityRecovery.grad,ElasticityFiniteType.D,recovery_basis]

lemma coord_real_log (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ x,0 < f x) (i : Fin 3) :
    coord i (smoothLog f hf hp)=
      smoothInv (smoothOfReal f hf) (fun x => Complex.ofReal_ne_zero.mpr (hp x).ne')*
        coord i (smoothOfReal f hf) := by
  apply Subtype.ext
  funext x
  rw [smoothLog,coord_ofReal]
  rw [fderiv.log ((hf.differentiable (by simp)) x) (hp x).ne']
  simp only [smul_apply,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_inv]
  change (f x : ℂ)⁻¹*(fderiv ℝ f x (e i) : ℂ)=_
  change _ = (f x : ℂ)⁻¹ * (coord i (smoothOfReal f hf) : X → ℂ) x
  rw [coord_ofReal]
lemma direction_real_log (θ : Fin 3 → ℂ) (f : X → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ x,0 < f x) :
    direction (A := Smooth) coord θ (smoothLog f hf hp)=
      smoothInv (smoothOfReal f hf) (fun x => Complex.ofReal_ne_zero.mpr (hp x).ne')*
        direction (A := Smooth) coord θ (smoothOfReal f hf) := by
  simp only [direction,coord_real_log,Finset.mul_sum,Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro i _
  ring
lemma logarithmicGrad_root (m : X → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hp : ∀ x,0 < m x) (i : Fin 3) :
    logarithmicGrad (positiveRoot m hm hp) (positiveRoot_nonzero m hm hp) i=coord i (smoothLog m hm hp) := by
  rw [coord_real_log]
  have hderiv := congrArg (coord i) (positiveRoot_square m hm hp)
  rw [partial_mul] at hderiv
  apply Subtype.ext
  funext point
  have hvalue := congrArg (fun value : Smooth => (value : X → ℂ) point) hderiv
  change (coord i (positiveRoot m hm hp) : X → ℂ) point * (Real.sqrt (m point) : ℂ) +
    (Real.sqrt (m point) : ℂ) * (coord i (positiveRoot m hm hp) : X → ℂ) point =
      (coord i (smoothOfReal m hm) : X → ℂ) point at hvalue
  change 2 * (Real.sqrt (m point) : ℂ)⁻¹ *
    (coord i (positiveRoot m hm hp) : X → ℂ) point =
      (m point : ℂ)⁻¹ * (coord i (smoothOfReal m hm) : X → ℂ) point
  have hroot : (Real.sqrt (m point) : ℂ)^2=(m point : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (hp point).le
  have hzero : (Real.sqrt (m point) : ℂ)≠0 := positiveRoot_nonzero m hm hp point
  rw [← hvalue,← hroot]
  field_simp [hzero]
  ring

lemma ofReal_direction (θ : Fin 3 → ℂ) (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : X) :
    (direction (A := Smooth) coord θ (smoothOfReal f hf) : X → ℂ) x=ElasticityRecovery.dir θ f x := by
  simp only [direction,ElasticityRecovery.dir,dotProduct,Fin.sum_univ_three,
    Subalgebra.coe_add,Subalgebra.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,coord_ofReal_grad]

lemma smoothLog_div (f g : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : ∀ x,0 < f x) (hq : ∀ x,0 < g x) :
    smoothLog (fun x => f x/g x) (hf.div hg (fun x => (hq x).ne')) (fun x => div_pos (hp x) (hq x))=
      smoothLog f hf hp-smoothLog g hg hq := by
  apply Subtype.ext
  funext x
  change (Real.log (f x/g x) : ℂ)=(Real.log (f x) : ℂ)-(Real.log (g x) : ℂ)
  exact_mod_cast Real.log_div (hp x).ne' (hq x).ne'

lemma direction_sub (θ : Fin 3 → ℂ) (f g : Smooth) :
    direction (A := Smooth) coord θ (f-g)=direction (A := Smooth) coord θ f-direction (A := Smooth) coord θ g :=
  map_sub (thetaDerivation θ) f g

lemma transportT_real (θ : Fin 3 → ℂ) (m k : X → ℝ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hk : ContDiff ℝ (⊤ : ℕ∞) k)
    (hmp : ∀ x,0 < m x) (hkp : ∀ x,0 < k x) (x : X) :
    (transportT θ (smoothOfReal k hk) (positiveRoot m hm hmp)
      (fun x => Complex.ofReal_ne_zero.mpr (hkp x).ne') (real_sum_nonzero m k hm hk hmp hkp) : X → ℂ) x=
      ElasticityRecovery.T m k x θ := by
  have hlog := smoothLog_div k (fun x => k x+m x) hk (hk.add hm) hkp (fun x => add_pos (hkp x) (hmp x))
  have hd := congrArg (direction (A := Smooth) coord θ) hlog
  rw [direction_sub] at hd
  conv_rhs at hd => rw [direction_real_log θ k hk hkp,
    direction_real_log θ (fun x => k x+m x) (hk.add hm) (fun x => add_pos (hkp x) (hmp x))]
  have hleft : (direction (A := Smooth) coord θ
      (smoothLog (fun x => k x/(k x+m x))
        (hk.div (hk.add hm) (fun x => (add_pos (hkp x) (hmp x)).ne'))
        (fun x => div_pos (hkp x) (add_pos (hkp x) (hmp x)))) : X → ℂ) x=
      ElasticityRecovery.T m k x θ := by
    exact ofReal_direction θ _ _ x
  rw [← hleft]
  change _ = (direction (A := Smooth) coord θ _ : X → ℂ) x
  rw [hd]
  unfold transportT
  simp only [positiveRoot_square,smoothOfReal_add]

lemma coord_real_grad (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) :
    coord i (smoothOfReal f hf)=smoothOfReal (fun x => ElasticityRecovery.grad f x i)
      (grad_contDiff f hf i) := by
  apply Subtype.ext
  funext x
  exact coord_ofReal_grad f hf i x
lemma direction_coord_real (θ : Fin 3 → ℂ) (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) (x : X) :
    (direction (A := Smooth) coord θ (coord i (smoothOfReal f hf)) : X → ℂ) x=
      ∑ j,θ j*(ElasticityRecovery.hessian f x i j : ℂ) := by
  rw [coord_real_grad,ofReal_direction]
  rfl
lemma thetaGamma_real (θ : Fin 3 → ℂ) (m : X → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hp : ∀ x,0 < m x) (x : X) :
    (thetaGamma θ (positiveRoot m hm hp) (positiveRoot_nonzero m hm hp) : X → ℂ) x=
      ElasticityRecovery.dir θ (fun x => Real.log (m x)) x := by
  simp only [thetaGamma,logarithmicGrad_root]
  exact ofReal_direction θ _ _ x
lemma transportQ_real (θ : Fin 3 → ℂ) (m k : X → ℝ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hk : ContDiff ℝ (⊤ : ℕ∞) k)
    (hmp : ∀ x,0 < m x) (hkp : ∀ x,0 < k x) (x : X) (i : Fin 3) :
    (transportQ θ (smoothOfReal k hk) (positiveRoot m hm hmp)
      (positiveRoot_nonzero m hm hmp) (fun x => Complex.ofReal_ne_zero.mpr (hkp x).ne')
      (real_sum_nonzero m k hm hk hmp hkp) i : X → ℂ) x=ElasticityRecovery.Q m k x θ i := by
  unfold transportQ
  simp only [positiveRoot_square,logarithmicGrad_root]
  rw [mul_assoc,← direction_real_log θ k hk hkp]
  simp only [Subalgebra.coe_sub,Subalgebra.coe_mul,Subalgebra.coe_smul,Pi.sub_apply,Pi.mul_apply,
    Pi.smul_apply,smul_eq_mul]
  rw [thetaGamma_real]
  have hdlog : (direction (A := Smooth) coord θ (smoothLog k hk hkp) : X → ℂ) x=
      ElasticityRecovery.dir θ (fun x => Real.log (k x)) x := ofReal_direction θ _ _ x
  rw [hdlog]
  change (1/2 : ℂ)*(((m x : ℂ)*((k x : ℂ)+(m x : ℂ))⁻¹*
      ElasticityRecovery.dir θ (fun x => Real.log (k x)) x-
      (1/2 : ℂ)*ElasticityRecovery.dir θ (fun x => Real.log (m x)) x)*
      (coord i (smoothLog m hm hmp) : X → ℂ) x-
      (m x : ℂ)*((k x : ℂ)+(m x : ℂ))⁻¹*
      (direction (A := Smooth) coord θ (coord i (smoothLog m hm hmp)) : X → ℂ) x)=_
  rw [smoothLog,coord_ofReal_grad,direction_coord_real]
  simp only [ElasticityRecovery.Q,ElasticityRecovery.QMatrix,ElasticityRecovery.dir,
    Matrix.mulVec,dotProduct,Fin.sum_univ_three,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_ofNat,Complex.ofReal_one]
  ring
end
open Set
open scoped BigOperators
end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CommonFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityAugmented
lemma smooth_sum_eval {ι : Type*} [Fintype ι] (f : ι → Smooth) (x : X) :
    ((∑ i,f i : Smooth) : X → ℂ) x=∑ i,(f i : X → ℂ) x := by
  exact map_sum ((Pi.evalRingHom (fun _ : X => ℂ) x).comp Smooth.val.toRingHom) f Finset.univ
end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Rigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix
namespace ElasticityConic

/-- The two affine charts exhaust every nonzero complex characteristic direction,
up to its nonzero scalar. No arbitrary choice of a square root is needed. -/
lemma chart_covers_null (v : C3) (hv : v≠0) (hn : null v) :
    ∃ (b : Bool) (z c : ℂ), c≠0 ∧ v=c • chartTheta b z := by
  have hn' : v 0^2+v 1^2+v 2^2=0 := by
    simpa only [null,dot3,pow_two] using hn
  let a : ℂ := v 0-Complex.I*v 1
  by_cases ha : a=0
  · have hz : v 2=0 := by
      have hh : v 2^2=0 := by
        dsimp [a] at ha
        linear_combination hn'-(v 0+Complex.I*v 1)*ha-(v 1)^2*Complex.I_sq
      exact (pow_eq_zero_iff (by omega : (2 : ℕ)≠0)).mp hh
    have hn0 : v 0≠0 := by
      intro h
      have h1 : v 1=0 := by
        have hh : Complex.I*v 1=0 := by simpa [a,h] using ha
        exact (mul_eq_zero.mp hh).resolve_left Complex.I_ne_zero
      apply hv
      ext i
      fin_cases i <;> simp [h,h1,hz]
    refine ⟨true,0,-v 0,neg_ne_zero.mpr hn0,?_⟩
    ext i
    fin_cases i <;> simp [chartTheta,chartZ₀,chartZ₁,theta,smul_eq_mul,hz]
    dsimp [a] at ha
    linear_combination Complex.I*ha+(v 1)*Complex.I_sq
  · have h0 : a^2-v 2^2=2*a*v 0 := by
      dsimp [a]
      linear_combination -hn'+(v 1)^2*Complex.I_sq
    have h1 : Complex.I*(a^2+v 2^2)=2*a*v 1 := by
      dsimp [a]
      linear_combination Complex.I*hn'+(Complex.I*(v 1)^2-2*v 0*v 1)*Complex.I_sq
    refine ⟨false,v 2/a,a/2,div_ne_zero ha (by norm_num),?_⟩
    ext i
    fin_cases i <;> simp [chartTheta,chartZ₀,chartZ₁,theta,smul_eq_mul]
    · field_simp
      linear_combination -h0
    · field_simp
      linear_combination -h1
    · field_simp
end ElasticityConic

end
end
section
noncomputable section
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

lemma chart_bottom_equal (b : Bool) (z : ℂ) (T₀ T₁ : Smooth) (Q₀ Q₁ : Fin 3 → Smooth)
    (he : chartMatrix b z T₀ Q₀=chartMatrix b z T₁ Q₁) (x : X) :
    (T₀ : X → ℂ) x=(T₁ : X → ℂ) x ∧
    ∀ p : C3, dotProduct (chartTheta b z) p=0 →
      dotProduct (fun i => (Q₀ i : X → ℂ) x) p=dotProduct (fun i => (Q₁ i : X → ℂ) x) p := by
  have ht := congrArg (fun M : Matrix (Fin 3) (Fin 3) Smooth => (M 2 2 : X → ℂ) x) he
  have h0 : dotProduct (fun i => (Q₀ i : X → ℂ) x) (h₁ (chartZ₀ b z) (chartZ₁ b z))=
      dotProduct (fun i => (Q₁ i : X → ℂ) x) (h₁ (chartZ₀ b z) (chartZ₁ b z)) := by
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) Smooth => (M 2 0 : X → ℂ) x) he
    simpa [chartMatrix,smooth_sum_eval,dotProduct,mul_comm] using hh
  have h1 : dotProduct (fun i => (Q₀ i : X → ℂ) x) (h₂ (chartZ₀ b z) (chartZ₁ b z))=
      dotProduct (fun i => (Q₁ i : X → ℂ) x) (h₂ (chartZ₀ b z) (chartZ₁ b z)) := by
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) Smooth => (M 2 1 : X → ℂ) x) he
    simpa [chartMatrix,smooth_sum_eval,dotProduct,mul_comm] using hh
  refine ⟨ht,?_⟩
  intro p hp
  have hs := congrArg Prod.fst (chartVector_coord b z (p,0) hp)
  change _+_=p at hs
  rw [← hs,dotProduct_add,dotProduct_add,dotProduct_smul,dotProduct_smul,
    dotProduct_smul,dotProduct_smul,h0,h1]

end ElasticityConic
namespace ElasticityRecovery
open ElasticityConic
lemma T_smul (m k : X → ℝ) (x : X) (c : ℂ) (θ : C3) :
    T m k x (c • θ)=c*T m k x θ := by
  simp only [T,dir,smul_dotProduct,smul_eq_mul]
lemma Q_smul (m k : X → ℝ) (x : X) (c : ℂ) (θ : C3) :
    Q m k x (c • θ)=c • Q m k x θ := by
  exact Matrix.mulVec_smul _ _ _
end ElasticityRecovery
namespace ElasticityAugmented
open ElasticityConic
/-- Equality of the actual conic connections is precisely sufficient for the
restricted physical transports used by Lamé coefficient recovery. -/
theorem restricted_transports_of_chart_equal_oai (m k : Fin 2 → X → ℝ)
    (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q)) (hk : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (k q))
    (hmp : ∀ q x,0 < m q x) (hkp : ∀ q x,0 < k q x)
    (he : ∀ b z,
      chartMatrix b z
        (transportT (chartTheta b z) (smoothOfReal (k 0) (hk 0)) (positiveRoot (m 0) (hm 0) (hmp 0))
          (fun x => Complex.ofReal_ne_zero.mpr (hkp 0 x).ne') (real_sum_nonzero (m 0) (k 0) (hm 0) (hk 0) (hmp 0) (hkp 0)))
        (transportQ (chartTheta b z) (smoothOfReal (k 0) (hk 0)) (positiveRoot (m 0) (hm 0) (hmp 0))
          (positiveRoot_nonzero (m 0) (hm 0) (hmp 0)) (fun x => Complex.ofReal_ne_zero.mpr (hkp 0 x).ne')
          (real_sum_nonzero (m 0) (k 0) (hm 0) (hk 0) (hmp 0) (hkp 0)))=
      chartMatrix b z
        (transportT (chartTheta b z) (smoothOfReal (k 1) (hk 1)) (positiveRoot (m 1) (hm 1) (hmp 1))
          (fun x => Complex.ofReal_ne_zero.mpr (hkp 1 x).ne') (real_sum_nonzero (m 1) (k 1) (hm 1) (hk 1) (hmp 1) (hkp 1)))
        (transportQ (chartTheta b z) (smoothOfReal (k 1) (hk 1)) (positiveRoot (m 1) (hm 1) (hmp 1))
          (positiveRoot_nonzero (m 1) (hm 1) (hmp 1)) (fun x => Complex.ofReal_ne_zero.mpr (hkp 1 x).ne')
          (real_sum_nonzero (m 1) (k 1) (hm 1) (hk 1) (hmp 1) (hkp 1)))) :
    ElasticityRecovery.EqualRestrictedTransports (m 0) (k 0) (m 1) (k 1) := by
  intro x θ hθ hn
  obtain ⟨b,z,c,hc,hθc⟩ := chart_covers_null θ hθ hn
  have hh := chart_bottom_equal b z _ _ _ _ (he b z) x
  have ht : ElasticityRecovery.T (m 0) (k 0) x (chartTheta b z)=
      ElasticityRecovery.T (m 1) (k 1) x (chartTheta b z) :=
    (transportT_real (chartTheta b z) (m 0) (k 0) (hm 0) (hk 0) (hmp 0) (hkp 0) x).symm.trans
      (hh.1.trans (transportT_real (chartTheta b z) (m 1) (k 1) (hm 1) (hk 1) (hmp 1) (hkp 1) x))
  have hq (q : Fin 2) : (fun i =>
      (transportQ (chartTheta b z) (smoothOfReal (k q) (hk q)) (positiveRoot (m q) (hm q) (hmp q))
        (positiveRoot_nonzero (m q) (hm q) (hmp q)) (fun x => Complex.ofReal_ne_zero.mpr (hkp q x).ne')
        (real_sum_nonzero (m q) (k q) (hm q) (hk q) (hmp q) (hkp q)) i : X → ℂ) x)=
      ElasticityRecovery.Q (m q) (k q) x (chartTheta b z) := by
    funext i
    exact transportQ_real (chartTheta b z) (m q) (k q) (hm q) (hk q) (hmp q) (hkp q) x i
  constructor
  · rw [hθc,ElasticityRecovery.T_smul,ElasticityRecovery.T_smul,ht]
  · intro p hp
    have hp' : dotProduct (chartTheta b z) p=0 := by
      rw [hθc,smul_dotProduct,smul_eq_mul] at hp
      exact (mul_eq_zero.mp hp).resolve_left hc
    have h := hh.2 p hp'
    rw [hq 0,hq 1] at h
    rw [hθc,ElasticityRecovery.Q_smul,ElasticityRecovery.Q_smul,smul_dotProduct,smul_dotProduct,h]
end ElasticityAugmented

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityAugmented.restricted_transports_of_chart_equal_oai := @OAI.ElasticityAugmented.restricted_transports_of_chart_equal_oai
