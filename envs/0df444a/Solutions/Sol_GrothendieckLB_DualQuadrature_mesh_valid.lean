-- Prove2me | solution 1 for GrothendieckLB.DualQuadrature.mesh_valid
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T16:33:56.729461+00:00
-- url     : https://prove2.me/submissions/9ec09925-ce45-495a-9226-a5c97448e35f

import Definitions.Def_GrothendieckLB_DualQuadratureMesh

namespace GrothendieckLB.DualQuadrature
set_option maxRecDepth 10000
lemma ndOk200 : nodeCheck nd200=true := by decide +kernel
lemma restOk200 : chainCheck rest200=true := Bool.and_eq_true_iff.mpr ⟨ndOk200,by decide +kernel⟩
lemma ndOk199 : nodeCheck nd199=true := by decide +kernel
lemma edgeOk199 : edgeCheck nd199 nd200=true := by decide +kernel
lemma restOk199 : chainCheck rest199=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk199,edgeOk199⟩,restOk200⟩
lemma ndOk198 : nodeCheck nd198=true := by decide +kernel
lemma edgeOk198 : edgeCheck nd198 nd199=true := by decide +kernel
lemma restOk198 : chainCheck rest198=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk198,edgeOk198⟩,restOk199⟩
lemma ndOk197 : nodeCheck nd197=true := by decide +kernel
lemma edgeOk197 : edgeCheck nd197 nd198=true := by decide +kernel
lemma restOk197 : chainCheck rest197=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk197,edgeOk197⟩,restOk198⟩
lemma ndOk196 : nodeCheck nd196=true := by decide +kernel
lemma edgeOk196 : edgeCheck nd196 nd197=true := by decide +kernel
lemma restOk196 : chainCheck rest196=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk196,edgeOk196⟩,restOk197⟩
lemma ndOk195 : nodeCheck nd195=true := by decide +kernel
lemma edgeOk195 : edgeCheck nd195 nd196=true := by decide +kernel
lemma restOk195 : chainCheck rest195=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk195,edgeOk195⟩,restOk196⟩
lemma ndOk194 : nodeCheck nd194=true := by decide +kernel
lemma edgeOk194 : edgeCheck nd194 nd195=true := by decide +kernel
lemma restOk194 : chainCheck rest194=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk194,edgeOk194⟩,restOk195⟩
lemma ndOk193 : nodeCheck nd193=true := by decide +kernel
lemma edgeOk193 : edgeCheck nd193 nd194=true := by decide +kernel
lemma restOk193 : chainCheck rest193=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk193,edgeOk193⟩,restOk194⟩
lemma ndOk192 : nodeCheck nd192=true := by decide +kernel
lemma edgeOk192 : edgeCheck nd192 nd193=true := by decide +kernel
lemma restOk192 : chainCheck rest192=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk192,edgeOk192⟩,restOk193⟩
lemma ndOk191 : nodeCheck nd191=true := by decide +kernel
lemma edgeOk191 : edgeCheck nd191 nd192=true := by decide +kernel
lemma restOk191 : chainCheck rest191=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk191,edgeOk191⟩,restOk192⟩
lemma ndOk190 : nodeCheck nd190=true := by decide +kernel
lemma edgeOk190 : edgeCheck nd190 nd191=true := by decide +kernel
lemma restOk190 : chainCheck rest190=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk190,edgeOk190⟩,restOk191⟩
lemma ndOk189 : nodeCheck nd189=true := by decide +kernel
lemma edgeOk189 : edgeCheck nd189 nd190=true := by decide +kernel
lemma restOk189 : chainCheck rest189=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk189,edgeOk189⟩,restOk190⟩
lemma ndOk188 : nodeCheck nd188=true := by decide +kernel
lemma edgeOk188 : edgeCheck nd188 nd189=true := by decide +kernel
lemma restOk188 : chainCheck rest188=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk188,edgeOk188⟩,restOk189⟩
lemma ndOk187 : nodeCheck nd187=true := by decide +kernel
lemma edgeOk187 : edgeCheck nd187 nd188=true := by decide +kernel
lemma restOk187 : chainCheck rest187=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk187,edgeOk187⟩,restOk188⟩
lemma ndOk186 : nodeCheck nd186=true := by decide +kernel
lemma edgeOk186 : edgeCheck nd186 nd187=true := by decide +kernel
lemma restOk186 : chainCheck rest186=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk186,edgeOk186⟩,restOk187⟩
lemma ndOk185 : nodeCheck nd185=true := by decide +kernel
lemma edgeOk185 : edgeCheck nd185 nd186=true := by decide +kernel
lemma restOk185 : chainCheck rest185=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk185,edgeOk185⟩,restOk186⟩
lemma ndOk184 : nodeCheck nd184=true := by decide +kernel
lemma edgeOk184 : edgeCheck nd184 nd185=true := by decide +kernel
lemma restOk184 : chainCheck rest184=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk184,edgeOk184⟩,restOk185⟩
lemma ndOk183 : nodeCheck nd183=true := by decide +kernel
lemma edgeOk183 : edgeCheck nd183 nd184=true := by decide +kernel
lemma restOk183 : chainCheck rest183=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk183,edgeOk183⟩,restOk184⟩
lemma ndOk182 : nodeCheck nd182=true := by decide +kernel
lemma edgeOk182 : edgeCheck nd182 nd183=true := by decide +kernel
lemma restOk182 : chainCheck rest182=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk182,edgeOk182⟩,restOk183⟩
lemma ndOk181 : nodeCheck nd181=true := by decide +kernel
lemma edgeOk181 : edgeCheck nd181 nd182=true := by decide +kernel
lemma restOk181 : chainCheck rest181=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk181,edgeOk181⟩,restOk182⟩
lemma ndOk180 : nodeCheck nd180=true := by decide +kernel
lemma edgeOk180 : edgeCheck nd180 nd181=true := by decide +kernel
lemma restOk180 : chainCheck rest180=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk180,edgeOk180⟩,restOk181⟩
lemma ndOk179 : nodeCheck nd179=true := by decide +kernel
lemma edgeOk179 : edgeCheck nd179 nd180=true := by decide +kernel
lemma restOk179 : chainCheck rest179=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk179,edgeOk179⟩,restOk180⟩
lemma ndOk178 : nodeCheck nd178=true := by decide +kernel
lemma edgeOk178 : edgeCheck nd178 nd179=true := by decide +kernel
lemma restOk178 : chainCheck rest178=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk178,edgeOk178⟩,restOk179⟩
lemma ndOk177 : nodeCheck nd177=true := by decide +kernel
lemma edgeOk177 : edgeCheck nd177 nd178=true := by decide +kernel
lemma restOk177 : chainCheck rest177=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk177,edgeOk177⟩,restOk178⟩
lemma ndOk176 : nodeCheck nd176=true := by decide +kernel
lemma edgeOk176 : edgeCheck nd176 nd177=true := by decide +kernel
lemma restOk176 : chainCheck rest176=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk176,edgeOk176⟩,restOk177⟩
lemma ndOk175 : nodeCheck nd175=true := by decide +kernel
lemma edgeOk175 : edgeCheck nd175 nd176=true := by decide +kernel
lemma restOk175 : chainCheck rest175=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk175,edgeOk175⟩,restOk176⟩
lemma ndOk174 : nodeCheck nd174=true := by decide +kernel
lemma edgeOk174 : edgeCheck nd174 nd175=true := by decide +kernel
lemma restOk174 : chainCheck rest174=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk174,edgeOk174⟩,restOk175⟩
lemma ndOk173 : nodeCheck nd173=true := by decide +kernel
lemma edgeOk173 : edgeCheck nd173 nd174=true := by decide +kernel
lemma restOk173 : chainCheck rest173=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk173,edgeOk173⟩,restOk174⟩
lemma ndOk172 : nodeCheck nd172=true := by decide +kernel
lemma edgeOk172 : edgeCheck nd172 nd173=true := by decide +kernel
lemma restOk172 : chainCheck rest172=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk172,edgeOk172⟩,restOk173⟩
lemma ndOk171 : nodeCheck nd171=true := by decide +kernel
lemma edgeOk171 : edgeCheck nd171 nd172=true := by decide +kernel
lemma restOk171 : chainCheck rest171=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk171,edgeOk171⟩,restOk172⟩
lemma ndOk170 : nodeCheck nd170=true := by decide +kernel
lemma edgeOk170 : edgeCheck nd170 nd171=true := by decide +kernel
lemma restOk170 : chainCheck rest170=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk170,edgeOk170⟩,restOk171⟩
lemma ndOk169 : nodeCheck nd169=true := by decide +kernel
lemma edgeOk169 : edgeCheck nd169 nd170=true := by decide +kernel
lemma restOk169 : chainCheck rest169=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk169,edgeOk169⟩,restOk170⟩
lemma ndOk168 : nodeCheck nd168=true := by decide +kernel
lemma edgeOk168 : edgeCheck nd168 nd169=true := by decide +kernel
lemma restOk168 : chainCheck rest168=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk168,edgeOk168⟩,restOk169⟩
lemma ndOk167 : nodeCheck nd167=true := by decide +kernel
lemma edgeOk167 : edgeCheck nd167 nd168=true := by decide +kernel
lemma restOk167 : chainCheck rest167=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk167,edgeOk167⟩,restOk168⟩
lemma ndOk166 : nodeCheck nd166=true := by decide +kernel
lemma edgeOk166 : edgeCheck nd166 nd167=true := by decide +kernel
lemma restOk166 : chainCheck rest166=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk166,edgeOk166⟩,restOk167⟩
lemma ndOk165 : nodeCheck nd165=true := by decide +kernel
lemma edgeOk165 : edgeCheck nd165 nd166=true := by decide +kernel
lemma restOk165 : chainCheck rest165=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk165,edgeOk165⟩,restOk166⟩
lemma ndOk164 : nodeCheck nd164=true := by decide +kernel
lemma edgeOk164 : edgeCheck nd164 nd165=true := by decide +kernel
lemma restOk164 : chainCheck rest164=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk164,edgeOk164⟩,restOk165⟩
lemma ndOk163 : nodeCheck nd163=true := by decide +kernel
lemma edgeOk163 : edgeCheck nd163 nd164=true := by decide +kernel
lemma restOk163 : chainCheck rest163=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk163,edgeOk163⟩,restOk164⟩
lemma ndOk162 : nodeCheck nd162=true := by decide +kernel
lemma edgeOk162 : edgeCheck nd162 nd163=true := by decide +kernel
lemma restOk162 : chainCheck rest162=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk162,edgeOk162⟩,restOk163⟩
lemma ndOk161 : nodeCheck nd161=true := by decide +kernel
lemma edgeOk161 : edgeCheck nd161 nd162=true := by decide +kernel
lemma restOk161 : chainCheck rest161=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk161,edgeOk161⟩,restOk162⟩
lemma ndOk160 : nodeCheck nd160=true := by decide +kernel
lemma edgeOk160 : edgeCheck nd160 nd161=true := by decide +kernel
lemma restOk160 : chainCheck rest160=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk160,edgeOk160⟩,restOk161⟩
lemma ndOk159 : nodeCheck nd159=true := by decide +kernel
lemma edgeOk159 : edgeCheck nd159 nd160=true := by decide +kernel
lemma restOk159 : chainCheck rest159=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk159,edgeOk159⟩,restOk160⟩
lemma ndOk158 : nodeCheck nd158=true := by decide +kernel
lemma edgeOk158 : edgeCheck nd158 nd159=true := by decide +kernel
lemma restOk158 : chainCheck rest158=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk158,edgeOk158⟩,restOk159⟩
lemma ndOk157 : nodeCheck nd157=true := by decide +kernel
lemma edgeOk157 : edgeCheck nd157 nd158=true := by decide +kernel
lemma restOk157 : chainCheck rest157=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk157,edgeOk157⟩,restOk158⟩
lemma ndOk156 : nodeCheck nd156=true := by decide +kernel
lemma edgeOk156 : edgeCheck nd156 nd157=true := by decide +kernel
lemma restOk156 : chainCheck rest156=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk156,edgeOk156⟩,restOk157⟩
lemma ndOk155 : nodeCheck nd155=true := by decide +kernel
lemma edgeOk155 : edgeCheck nd155 nd156=true := by decide +kernel
lemma restOk155 : chainCheck rest155=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk155,edgeOk155⟩,restOk156⟩
lemma ndOk154 : nodeCheck nd154=true := by decide +kernel
lemma edgeOk154 : edgeCheck nd154 nd155=true := by decide +kernel
lemma restOk154 : chainCheck rest154=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk154,edgeOk154⟩,restOk155⟩
lemma ndOk153 : nodeCheck nd153=true := by decide +kernel
lemma edgeOk153 : edgeCheck nd153 nd154=true := by decide +kernel
lemma restOk153 : chainCheck rest153=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk153,edgeOk153⟩,restOk154⟩
lemma ndOk152 : nodeCheck nd152=true := by decide +kernel
lemma edgeOk152 : edgeCheck nd152 nd153=true := by decide +kernel
lemma restOk152 : chainCheck rest152=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk152,edgeOk152⟩,restOk153⟩
lemma ndOk151 : nodeCheck nd151=true := by decide +kernel
lemma edgeOk151 : edgeCheck nd151 nd152=true := by decide +kernel
lemma restOk151 : chainCheck rest151=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk151,edgeOk151⟩,restOk152⟩
lemma ndOk150 : nodeCheck nd150=true := by decide +kernel
lemma edgeOk150 : edgeCheck nd150 nd151=true := by decide +kernel
lemma restOk150 : chainCheck rest150=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk150,edgeOk150⟩,restOk151⟩
lemma ndOk149 : nodeCheck nd149=true := by decide +kernel
lemma edgeOk149 : edgeCheck nd149 nd150=true := by decide +kernel
lemma restOk149 : chainCheck rest149=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk149,edgeOk149⟩,restOk150⟩
lemma ndOk148 : nodeCheck nd148=true := by decide +kernel
lemma edgeOk148 : edgeCheck nd148 nd149=true := by decide +kernel
lemma restOk148 : chainCheck rest148=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk148,edgeOk148⟩,restOk149⟩
lemma ndOk147 : nodeCheck nd147=true := by decide +kernel
lemma edgeOk147 : edgeCheck nd147 nd148=true := by decide +kernel
lemma restOk147 : chainCheck rest147=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk147,edgeOk147⟩,restOk148⟩
lemma ndOk146 : nodeCheck nd146=true := by decide +kernel
lemma edgeOk146 : edgeCheck nd146 nd147=true := by decide +kernel
lemma restOk146 : chainCheck rest146=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk146,edgeOk146⟩,restOk147⟩
lemma ndOk145 : nodeCheck nd145=true := by decide +kernel
lemma edgeOk145 : edgeCheck nd145 nd146=true := by decide +kernel
lemma restOk145 : chainCheck rest145=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk145,edgeOk145⟩,restOk146⟩
lemma ndOk144 : nodeCheck nd144=true := by decide +kernel
lemma edgeOk144 : edgeCheck nd144 nd145=true := by decide +kernel
lemma restOk144 : chainCheck rest144=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk144,edgeOk144⟩,restOk145⟩
lemma ndOk143 : nodeCheck nd143=true := by decide +kernel
lemma edgeOk143 : edgeCheck nd143 nd144=true := by decide +kernel
lemma restOk143 : chainCheck rest143=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk143,edgeOk143⟩,restOk144⟩
lemma ndOk142 : nodeCheck nd142=true := by decide +kernel
lemma edgeOk142 : edgeCheck nd142 nd143=true := by decide +kernel
lemma restOk142 : chainCheck rest142=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk142,edgeOk142⟩,restOk143⟩
lemma ndOk141 : nodeCheck nd141=true := by decide +kernel
lemma edgeOk141 : edgeCheck nd141 nd142=true := by decide +kernel
lemma restOk141 : chainCheck rest141=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk141,edgeOk141⟩,restOk142⟩
lemma ndOk140 : nodeCheck nd140=true := by decide +kernel
lemma edgeOk140 : edgeCheck nd140 nd141=true := by decide +kernel
lemma restOk140 : chainCheck rest140=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk140,edgeOk140⟩,restOk141⟩
lemma ndOk139 : nodeCheck nd139=true := by decide +kernel
lemma edgeOk139 : edgeCheck nd139 nd140=true := by decide +kernel
lemma restOk139 : chainCheck rest139=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk139,edgeOk139⟩,restOk140⟩
lemma ndOk138 : nodeCheck nd138=true := by decide +kernel
lemma edgeOk138 : edgeCheck nd138 nd139=true := by decide +kernel
lemma restOk138 : chainCheck rest138=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk138,edgeOk138⟩,restOk139⟩
lemma ndOk137 : nodeCheck nd137=true := by decide +kernel
lemma edgeOk137 : edgeCheck nd137 nd138=true := by decide +kernel
lemma restOk137 : chainCheck rest137=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk137,edgeOk137⟩,restOk138⟩
lemma ndOk136 : nodeCheck nd136=true := by decide +kernel
lemma edgeOk136 : edgeCheck nd136 nd137=true := by decide +kernel
lemma restOk136 : chainCheck rest136=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk136,edgeOk136⟩,restOk137⟩
lemma ndOk135 : nodeCheck nd135=true := by decide +kernel
lemma edgeOk135 : edgeCheck nd135 nd136=true := by decide +kernel
lemma restOk135 : chainCheck rest135=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk135,edgeOk135⟩,restOk136⟩
lemma ndOk134 : nodeCheck nd134=true := by decide +kernel
lemma edgeOk134 : edgeCheck nd134 nd135=true := by decide +kernel
lemma restOk134 : chainCheck rest134=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk134,edgeOk134⟩,restOk135⟩
lemma ndOk133 : nodeCheck nd133=true := by decide +kernel
lemma edgeOk133 : edgeCheck nd133 nd134=true := by decide +kernel
lemma restOk133 : chainCheck rest133=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk133,edgeOk133⟩,restOk134⟩
lemma ndOk132 : nodeCheck nd132=true := by decide +kernel
lemma edgeOk132 : edgeCheck nd132 nd133=true := by decide +kernel
lemma restOk132 : chainCheck rest132=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk132,edgeOk132⟩,restOk133⟩
lemma ndOk131 : nodeCheck nd131=true := by decide +kernel
lemma edgeOk131 : edgeCheck nd131 nd132=true := by decide +kernel
lemma restOk131 : chainCheck rest131=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk131,edgeOk131⟩,restOk132⟩
lemma ndOk130 : nodeCheck nd130=true := by decide +kernel
lemma edgeOk130 : edgeCheck nd130 nd131=true := by decide +kernel
lemma restOk130 : chainCheck rest130=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk130,edgeOk130⟩,restOk131⟩
lemma ndOk129 : nodeCheck nd129=true := by decide +kernel
lemma edgeOk129 : edgeCheck nd129 nd130=true := by decide +kernel
lemma restOk129 : chainCheck rest129=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk129,edgeOk129⟩,restOk130⟩
lemma ndOk128 : nodeCheck nd128=true := by decide +kernel
lemma edgeOk128 : edgeCheck nd128 nd129=true := by decide +kernel
lemma restOk128 : chainCheck rest128=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk128,edgeOk128⟩,restOk129⟩
lemma ndOk127 : nodeCheck nd127=true := by decide +kernel
lemma edgeOk127 : edgeCheck nd127 nd128=true := by decide +kernel
lemma restOk127 : chainCheck rest127=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk127,edgeOk127⟩,restOk128⟩
lemma ndOk126 : nodeCheck nd126=true := by decide +kernel
lemma edgeOk126 : edgeCheck nd126 nd127=true := by decide +kernel
lemma restOk126 : chainCheck rest126=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk126,edgeOk126⟩,restOk127⟩
lemma ndOk125 : nodeCheck nd125=true := by decide +kernel
lemma edgeOk125 : edgeCheck nd125 nd126=true := by decide +kernel
lemma restOk125 : chainCheck rest125=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk125,edgeOk125⟩,restOk126⟩
lemma ndOk124 : nodeCheck nd124=true := by decide +kernel
lemma edgeOk124 : edgeCheck nd124 nd125=true := by decide +kernel
lemma restOk124 : chainCheck rest124=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk124,edgeOk124⟩,restOk125⟩
lemma ndOk123 : nodeCheck nd123=true := by decide +kernel
lemma edgeOk123 : edgeCheck nd123 nd124=true := by decide +kernel
lemma restOk123 : chainCheck rest123=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk123,edgeOk123⟩,restOk124⟩
lemma ndOk122 : nodeCheck nd122=true := by decide +kernel
lemma edgeOk122 : edgeCheck nd122 nd123=true := by decide +kernel
lemma restOk122 : chainCheck rest122=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk122,edgeOk122⟩,restOk123⟩
lemma ndOk121 : nodeCheck nd121=true := by decide +kernel
lemma edgeOk121 : edgeCheck nd121 nd122=true := by decide +kernel
lemma restOk121 : chainCheck rest121=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk121,edgeOk121⟩,restOk122⟩
lemma ndOk120 : nodeCheck nd120=true := by decide +kernel
lemma edgeOk120 : edgeCheck nd120 nd121=true := by decide +kernel
lemma restOk120 : chainCheck rest120=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk120,edgeOk120⟩,restOk121⟩
lemma ndOk119 : nodeCheck nd119=true := by decide +kernel
lemma edgeOk119 : edgeCheck nd119 nd120=true := by decide +kernel
lemma restOk119 : chainCheck rest119=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk119,edgeOk119⟩,restOk120⟩
lemma ndOk118 : nodeCheck nd118=true := by decide +kernel
lemma edgeOk118 : edgeCheck nd118 nd119=true := by decide +kernel
lemma restOk118 : chainCheck rest118=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk118,edgeOk118⟩,restOk119⟩
lemma ndOk117 : nodeCheck nd117=true := by decide +kernel
lemma edgeOk117 : edgeCheck nd117 nd118=true := by decide +kernel
lemma restOk117 : chainCheck rest117=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk117,edgeOk117⟩,restOk118⟩
lemma ndOk116 : nodeCheck nd116=true := by decide +kernel
lemma edgeOk116 : edgeCheck nd116 nd117=true := by decide +kernel
lemma restOk116 : chainCheck rest116=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk116,edgeOk116⟩,restOk117⟩
lemma ndOk115 : nodeCheck nd115=true := by decide +kernel
lemma edgeOk115 : edgeCheck nd115 nd116=true := by decide +kernel
lemma restOk115 : chainCheck rest115=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk115,edgeOk115⟩,restOk116⟩
lemma ndOk114 : nodeCheck nd114=true := by decide +kernel
lemma edgeOk114 : edgeCheck nd114 nd115=true := by decide +kernel
lemma restOk114 : chainCheck rest114=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk114,edgeOk114⟩,restOk115⟩
lemma ndOk113 : nodeCheck nd113=true := by decide +kernel
lemma edgeOk113 : edgeCheck nd113 nd114=true := by decide +kernel
lemma restOk113 : chainCheck rest113=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk113,edgeOk113⟩,restOk114⟩
lemma ndOk112 : nodeCheck nd112=true := by decide +kernel
lemma edgeOk112 : edgeCheck nd112 nd113=true := by decide +kernel
lemma restOk112 : chainCheck rest112=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk112,edgeOk112⟩,restOk113⟩
lemma ndOk111 : nodeCheck nd111=true := by decide +kernel
lemma edgeOk111 : edgeCheck nd111 nd112=true := by decide +kernel
lemma restOk111 : chainCheck rest111=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk111,edgeOk111⟩,restOk112⟩
lemma ndOk110 : nodeCheck nd110=true := by decide +kernel
lemma edgeOk110 : edgeCheck nd110 nd111=true := by decide +kernel
lemma restOk110 : chainCheck rest110=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk110,edgeOk110⟩,restOk111⟩
lemma ndOk109 : nodeCheck nd109=true := by decide +kernel
lemma edgeOk109 : edgeCheck nd109 nd110=true := by decide +kernel
lemma restOk109 : chainCheck rest109=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk109,edgeOk109⟩,restOk110⟩
lemma ndOk108 : nodeCheck nd108=true := by decide +kernel
lemma edgeOk108 : edgeCheck nd108 nd109=true := by decide +kernel
lemma restOk108 : chainCheck rest108=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk108,edgeOk108⟩,restOk109⟩
lemma ndOk107 : nodeCheck nd107=true := by decide +kernel
lemma edgeOk107 : edgeCheck nd107 nd108=true := by decide +kernel
lemma restOk107 : chainCheck rest107=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk107,edgeOk107⟩,restOk108⟩
lemma ndOk106 : nodeCheck nd106=true := by decide +kernel
lemma edgeOk106 : edgeCheck nd106 nd107=true := by decide +kernel
lemma restOk106 : chainCheck rest106=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk106,edgeOk106⟩,restOk107⟩
lemma ndOk105 : nodeCheck nd105=true := by decide +kernel
lemma edgeOk105 : edgeCheck nd105 nd106=true := by decide +kernel
lemma restOk105 : chainCheck rest105=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk105,edgeOk105⟩,restOk106⟩
lemma ndOk104 : nodeCheck nd104=true := by decide +kernel
lemma edgeOk104 : edgeCheck nd104 nd105=true := by decide +kernel
lemma restOk104 : chainCheck rest104=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk104,edgeOk104⟩,restOk105⟩
lemma ndOk103 : nodeCheck nd103=true := by decide +kernel
lemma edgeOk103 : edgeCheck nd103 nd104=true := by decide +kernel
lemma restOk103 : chainCheck rest103=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk103,edgeOk103⟩,restOk104⟩
lemma ndOk102 : nodeCheck nd102=true := by decide +kernel
lemma edgeOk102 : edgeCheck nd102 nd103=true := by decide +kernel
lemma restOk102 : chainCheck rest102=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk102,edgeOk102⟩,restOk103⟩
lemma ndOk101 : nodeCheck nd101=true := by decide +kernel
lemma edgeOk101 : edgeCheck nd101 nd102=true := by decide +kernel
lemma restOk101 : chainCheck rest101=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk101,edgeOk101⟩,restOk102⟩
lemma ndOk100 : nodeCheck nd100=true := by decide +kernel
lemma edgeOk100 : edgeCheck nd100 nd101=true := by decide +kernel
lemma restOk100 : chainCheck rest100=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk100,edgeOk100⟩,restOk101⟩
lemma ndOk99 : nodeCheck nd99=true := by decide +kernel
lemma edgeOk99 : edgeCheck nd99 nd100=true := by decide +kernel
lemma restOk99 : chainCheck rest99=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk99,edgeOk99⟩,restOk100⟩
lemma ndOk98 : nodeCheck nd98=true := by decide +kernel
lemma edgeOk98 : edgeCheck nd98 nd99=true := by decide +kernel
lemma restOk98 : chainCheck rest98=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk98,edgeOk98⟩,restOk99⟩
lemma ndOk97 : nodeCheck nd97=true := by decide +kernel
lemma edgeOk97 : edgeCheck nd97 nd98=true := by decide +kernel
lemma restOk97 : chainCheck rest97=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk97,edgeOk97⟩,restOk98⟩
lemma ndOk96 : nodeCheck nd96=true := by decide +kernel
lemma edgeOk96 : edgeCheck nd96 nd97=true := by decide +kernel
lemma restOk96 : chainCheck rest96=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk96,edgeOk96⟩,restOk97⟩
lemma ndOk95 : nodeCheck nd95=true := by decide +kernel
lemma edgeOk95 : edgeCheck nd95 nd96=true := by decide +kernel
lemma restOk95 : chainCheck rest95=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk95,edgeOk95⟩,restOk96⟩
lemma ndOk94 : nodeCheck nd94=true := by decide +kernel
lemma edgeOk94 : edgeCheck nd94 nd95=true := by decide +kernel
lemma restOk94 : chainCheck rest94=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk94,edgeOk94⟩,restOk95⟩
lemma ndOk93 : nodeCheck nd93=true := by decide +kernel
lemma edgeOk93 : edgeCheck nd93 nd94=true := by decide +kernel
lemma restOk93 : chainCheck rest93=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk93,edgeOk93⟩,restOk94⟩
lemma ndOk92 : nodeCheck nd92=true := by decide +kernel
lemma edgeOk92 : edgeCheck nd92 nd93=true := by decide +kernel
lemma restOk92 : chainCheck rest92=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk92,edgeOk92⟩,restOk93⟩
lemma ndOk91 : nodeCheck nd91=true := by decide +kernel
lemma edgeOk91 : edgeCheck nd91 nd92=true := by decide +kernel
lemma restOk91 : chainCheck rest91=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk91,edgeOk91⟩,restOk92⟩
lemma ndOk90 : nodeCheck nd90=true := by decide +kernel
lemma edgeOk90 : edgeCheck nd90 nd91=true := by decide +kernel
lemma restOk90 : chainCheck rest90=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk90,edgeOk90⟩,restOk91⟩
lemma ndOk89 : nodeCheck nd89=true := by decide +kernel
lemma edgeOk89 : edgeCheck nd89 nd90=true := by decide +kernel
lemma restOk89 : chainCheck rest89=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk89,edgeOk89⟩,restOk90⟩
lemma ndOk88 : nodeCheck nd88=true := by decide +kernel
lemma edgeOk88 : edgeCheck nd88 nd89=true := by decide +kernel
lemma restOk88 : chainCheck rest88=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk88,edgeOk88⟩,restOk89⟩
lemma ndOk87 : nodeCheck nd87=true := by decide +kernel
lemma edgeOk87 : edgeCheck nd87 nd88=true := by decide +kernel
lemma restOk87 : chainCheck rest87=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk87,edgeOk87⟩,restOk88⟩
lemma ndOk86 : nodeCheck nd86=true := by decide +kernel
lemma edgeOk86 : edgeCheck nd86 nd87=true := by decide +kernel
lemma restOk86 : chainCheck rest86=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk86,edgeOk86⟩,restOk87⟩
lemma ndOk85 : nodeCheck nd85=true := by decide +kernel
lemma edgeOk85 : edgeCheck nd85 nd86=true := by decide +kernel
lemma restOk85 : chainCheck rest85=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk85,edgeOk85⟩,restOk86⟩
lemma ndOk84 : nodeCheck nd84=true := by decide +kernel
lemma edgeOk84 : edgeCheck nd84 nd85=true := by decide +kernel
lemma restOk84 : chainCheck rest84=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk84,edgeOk84⟩,restOk85⟩
lemma ndOk83 : nodeCheck nd83=true := by decide +kernel
lemma edgeOk83 : edgeCheck nd83 nd84=true := by decide +kernel
lemma restOk83 : chainCheck rest83=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk83,edgeOk83⟩,restOk84⟩
lemma ndOk82 : nodeCheck nd82=true := by decide +kernel
lemma edgeOk82 : edgeCheck nd82 nd83=true := by decide +kernel
lemma restOk82 : chainCheck rest82=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk82,edgeOk82⟩,restOk83⟩
lemma ndOk81 : nodeCheck nd81=true := by decide +kernel
lemma edgeOk81 : edgeCheck nd81 nd82=true := by decide +kernel
lemma restOk81 : chainCheck rest81=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk81,edgeOk81⟩,restOk82⟩
lemma ndOk80 : nodeCheck nd80=true := by decide +kernel
lemma edgeOk80 : edgeCheck nd80 nd81=true := by decide +kernel
lemma restOk80 : chainCheck rest80=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk80,edgeOk80⟩,restOk81⟩
lemma ndOk79 : nodeCheck nd79=true := by decide +kernel
lemma edgeOk79 : edgeCheck nd79 nd80=true := by decide +kernel
lemma restOk79 : chainCheck rest79=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk79,edgeOk79⟩,restOk80⟩
lemma ndOk78 : nodeCheck nd78=true := by decide +kernel
lemma edgeOk78 : edgeCheck nd78 nd79=true := by decide +kernel
lemma restOk78 : chainCheck rest78=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk78,edgeOk78⟩,restOk79⟩
lemma ndOk77 : nodeCheck nd77=true := by decide +kernel
lemma edgeOk77 : edgeCheck nd77 nd78=true := by decide +kernel
lemma restOk77 : chainCheck rest77=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk77,edgeOk77⟩,restOk78⟩
lemma ndOk76 : nodeCheck nd76=true := by decide +kernel
lemma edgeOk76 : edgeCheck nd76 nd77=true := by decide +kernel
lemma restOk76 : chainCheck rest76=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk76,edgeOk76⟩,restOk77⟩
lemma ndOk75 : nodeCheck nd75=true := by decide +kernel
lemma edgeOk75 : edgeCheck nd75 nd76=true := by decide +kernel
lemma restOk75 : chainCheck rest75=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk75,edgeOk75⟩,restOk76⟩
lemma ndOk74 : nodeCheck nd74=true := by decide +kernel
lemma edgeOk74 : edgeCheck nd74 nd75=true := by decide +kernel
lemma restOk74 : chainCheck rest74=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk74,edgeOk74⟩,restOk75⟩
lemma ndOk73 : nodeCheck nd73=true := by decide +kernel
lemma edgeOk73 : edgeCheck nd73 nd74=true := by decide +kernel
lemma restOk73 : chainCheck rest73=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk73,edgeOk73⟩,restOk74⟩
lemma ndOk72 : nodeCheck nd72=true := by decide +kernel
lemma edgeOk72 : edgeCheck nd72 nd73=true := by decide +kernel
lemma restOk72 : chainCheck rest72=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk72,edgeOk72⟩,restOk73⟩
lemma ndOk71 : nodeCheck nd71=true := by decide +kernel
lemma edgeOk71 : edgeCheck nd71 nd72=true := by decide +kernel
lemma restOk71 : chainCheck rest71=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk71,edgeOk71⟩,restOk72⟩
lemma ndOk70 : nodeCheck nd70=true := by decide +kernel
lemma edgeOk70 : edgeCheck nd70 nd71=true := by decide +kernel
lemma restOk70 : chainCheck rest70=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk70,edgeOk70⟩,restOk71⟩
lemma ndOk69 : nodeCheck nd69=true := by decide +kernel
lemma edgeOk69 : edgeCheck nd69 nd70=true := by decide +kernel
lemma restOk69 : chainCheck rest69=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk69,edgeOk69⟩,restOk70⟩
lemma ndOk68 : nodeCheck nd68=true := by decide +kernel
lemma edgeOk68 : edgeCheck nd68 nd69=true := by decide +kernel
lemma restOk68 : chainCheck rest68=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk68,edgeOk68⟩,restOk69⟩
lemma ndOk67 : nodeCheck nd67=true := by decide +kernel
lemma edgeOk67 : edgeCheck nd67 nd68=true := by decide +kernel
lemma restOk67 : chainCheck rest67=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk67,edgeOk67⟩,restOk68⟩
lemma ndOk66 : nodeCheck nd66=true := by decide +kernel
lemma edgeOk66 : edgeCheck nd66 nd67=true := by decide +kernel
lemma restOk66 : chainCheck rest66=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk66,edgeOk66⟩,restOk67⟩
lemma ndOk65 : nodeCheck nd65=true := by decide +kernel
lemma edgeOk65 : edgeCheck nd65 nd66=true := by decide +kernel
lemma restOk65 : chainCheck rest65=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk65,edgeOk65⟩,restOk66⟩
lemma ndOk64 : nodeCheck nd64=true := by decide +kernel
lemma edgeOk64 : edgeCheck nd64 nd65=true := by decide +kernel
lemma restOk64 : chainCheck rest64=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk64,edgeOk64⟩,restOk65⟩
lemma ndOk63 : nodeCheck nd63=true := by decide +kernel
lemma edgeOk63 : edgeCheck nd63 nd64=true := by decide +kernel
lemma restOk63 : chainCheck rest63=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk63,edgeOk63⟩,restOk64⟩
lemma ndOk62 : nodeCheck nd62=true := by decide +kernel
lemma edgeOk62 : edgeCheck nd62 nd63=true := by decide +kernel
lemma restOk62 : chainCheck rest62=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk62,edgeOk62⟩,restOk63⟩
lemma ndOk61 : nodeCheck nd61=true := by decide +kernel
lemma edgeOk61 : edgeCheck nd61 nd62=true := by decide +kernel
lemma restOk61 : chainCheck rest61=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk61,edgeOk61⟩,restOk62⟩
lemma ndOk60 : nodeCheck nd60=true := by decide +kernel
lemma edgeOk60 : edgeCheck nd60 nd61=true := by decide +kernel
lemma restOk60 : chainCheck rest60=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk60,edgeOk60⟩,restOk61⟩
lemma ndOk59 : nodeCheck nd59=true := by decide +kernel
lemma edgeOk59 : edgeCheck nd59 nd60=true := by decide +kernel
lemma restOk59 : chainCheck rest59=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk59,edgeOk59⟩,restOk60⟩
lemma ndOk58 : nodeCheck nd58=true := by decide +kernel
lemma edgeOk58 : edgeCheck nd58 nd59=true := by decide +kernel
lemma restOk58 : chainCheck rest58=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk58,edgeOk58⟩,restOk59⟩
lemma ndOk57 : nodeCheck nd57=true := by decide +kernel
lemma edgeOk57 : edgeCheck nd57 nd58=true := by decide +kernel
lemma restOk57 : chainCheck rest57=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk57,edgeOk57⟩,restOk58⟩
lemma ndOk56 : nodeCheck nd56=true := by decide +kernel
lemma edgeOk56 : edgeCheck nd56 nd57=true := by decide +kernel
lemma restOk56 : chainCheck rest56=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk56,edgeOk56⟩,restOk57⟩
lemma ndOk55 : nodeCheck nd55=true := by decide +kernel
lemma edgeOk55 : edgeCheck nd55 nd56=true := by decide +kernel
lemma restOk55 : chainCheck rest55=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk55,edgeOk55⟩,restOk56⟩
lemma ndOk54 : nodeCheck nd54=true := by decide +kernel
lemma edgeOk54 : edgeCheck nd54 nd55=true := by decide +kernel
lemma restOk54 : chainCheck rest54=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk54,edgeOk54⟩,restOk55⟩
lemma ndOk53 : nodeCheck nd53=true := by decide +kernel
lemma edgeOk53 : edgeCheck nd53 nd54=true := by decide +kernel
lemma restOk53 : chainCheck rest53=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk53,edgeOk53⟩,restOk54⟩
lemma ndOk52 : nodeCheck nd52=true := by decide +kernel
lemma edgeOk52 : edgeCheck nd52 nd53=true := by decide +kernel
lemma restOk52 : chainCheck rest52=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk52,edgeOk52⟩,restOk53⟩
lemma ndOk51 : nodeCheck nd51=true := by decide +kernel
lemma edgeOk51 : edgeCheck nd51 nd52=true := by decide +kernel
lemma restOk51 : chainCheck rest51=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk51,edgeOk51⟩,restOk52⟩
lemma ndOk50 : nodeCheck nd50=true := by decide +kernel
lemma edgeOk50 : edgeCheck nd50 nd51=true := by decide +kernel
lemma restOk50 : chainCheck rest50=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk50,edgeOk50⟩,restOk51⟩
lemma ndOk49 : nodeCheck nd49=true := by decide +kernel
lemma edgeOk49 : edgeCheck nd49 nd50=true := by decide +kernel
lemma restOk49 : chainCheck rest49=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk49,edgeOk49⟩,restOk50⟩
lemma ndOk48 : nodeCheck nd48=true := by decide +kernel
lemma edgeOk48 : edgeCheck nd48 nd49=true := by decide +kernel
lemma restOk48 : chainCheck rest48=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk48,edgeOk48⟩,restOk49⟩
lemma ndOk47 : nodeCheck nd47=true := by decide +kernel
lemma edgeOk47 : edgeCheck nd47 nd48=true := by decide +kernel
lemma restOk47 : chainCheck rest47=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk47,edgeOk47⟩,restOk48⟩
lemma ndOk46 : nodeCheck nd46=true := by decide +kernel
lemma edgeOk46 : edgeCheck nd46 nd47=true := by decide +kernel
lemma restOk46 : chainCheck rest46=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk46,edgeOk46⟩,restOk47⟩
lemma ndOk45 : nodeCheck nd45=true := by decide +kernel
lemma edgeOk45 : edgeCheck nd45 nd46=true := by decide +kernel
lemma restOk45 : chainCheck rest45=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk45,edgeOk45⟩,restOk46⟩
lemma ndOk44 : nodeCheck nd44=true := by decide +kernel
lemma edgeOk44 : edgeCheck nd44 nd45=true := by decide +kernel
lemma restOk44 : chainCheck rest44=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk44,edgeOk44⟩,restOk45⟩
lemma ndOk43 : nodeCheck nd43=true := by decide +kernel
lemma edgeOk43 : edgeCheck nd43 nd44=true := by decide +kernel
lemma restOk43 : chainCheck rest43=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk43,edgeOk43⟩,restOk44⟩
lemma ndOk42 : nodeCheck nd42=true := by decide +kernel
lemma edgeOk42 : edgeCheck nd42 nd43=true := by decide +kernel
lemma restOk42 : chainCheck rest42=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk42,edgeOk42⟩,restOk43⟩
lemma ndOk41 : nodeCheck nd41=true := by decide +kernel
lemma edgeOk41 : edgeCheck nd41 nd42=true := by decide +kernel
lemma restOk41 : chainCheck rest41=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk41,edgeOk41⟩,restOk42⟩
lemma ndOk40 : nodeCheck nd40=true := by decide +kernel
lemma edgeOk40 : edgeCheck nd40 nd41=true := by decide +kernel
lemma restOk40 : chainCheck rest40=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk40,edgeOk40⟩,restOk41⟩
lemma ndOk39 : nodeCheck nd39=true := by decide +kernel
lemma edgeOk39 : edgeCheck nd39 nd40=true := by decide +kernel
lemma restOk39 : chainCheck rest39=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk39,edgeOk39⟩,restOk40⟩
lemma ndOk38 : nodeCheck nd38=true := by decide +kernel
lemma edgeOk38 : edgeCheck nd38 nd39=true := by decide +kernel
lemma restOk38 : chainCheck rest38=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk38,edgeOk38⟩,restOk39⟩
lemma ndOk37 : nodeCheck nd37=true := by decide +kernel
lemma edgeOk37 : edgeCheck nd37 nd38=true := by decide +kernel
lemma restOk37 : chainCheck rest37=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk37,edgeOk37⟩,restOk38⟩
lemma ndOk36 : nodeCheck nd36=true := by decide +kernel
lemma edgeOk36 : edgeCheck nd36 nd37=true := by decide +kernel
lemma restOk36 : chainCheck rest36=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk36,edgeOk36⟩,restOk37⟩
lemma ndOk35 : nodeCheck nd35=true := by decide +kernel
lemma edgeOk35 : edgeCheck nd35 nd36=true := by decide +kernel
lemma restOk35 : chainCheck rest35=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk35,edgeOk35⟩,restOk36⟩
lemma ndOk34 : nodeCheck nd34=true := by decide +kernel
lemma edgeOk34 : edgeCheck nd34 nd35=true := by decide +kernel
lemma restOk34 : chainCheck rest34=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk34,edgeOk34⟩,restOk35⟩
lemma ndOk33 : nodeCheck nd33=true := by decide +kernel
lemma edgeOk33 : edgeCheck nd33 nd34=true := by decide +kernel
lemma restOk33 : chainCheck rest33=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk33,edgeOk33⟩,restOk34⟩
lemma ndOk32 : nodeCheck nd32=true := by decide +kernel
lemma edgeOk32 : edgeCheck nd32 nd33=true := by decide +kernel
lemma restOk32 : chainCheck rest32=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk32,edgeOk32⟩,restOk33⟩
lemma ndOk31 : nodeCheck nd31=true := by decide +kernel
lemma edgeOk31 : edgeCheck nd31 nd32=true := by decide +kernel
lemma restOk31 : chainCheck rest31=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk31,edgeOk31⟩,restOk32⟩
lemma ndOk30 : nodeCheck nd30=true := by decide +kernel
lemma edgeOk30 : edgeCheck nd30 nd31=true := by decide +kernel
lemma restOk30 : chainCheck rest30=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk30,edgeOk30⟩,restOk31⟩
lemma ndOk29 : nodeCheck nd29=true := by decide +kernel
lemma edgeOk29 : edgeCheck nd29 nd30=true := by decide +kernel
lemma restOk29 : chainCheck rest29=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk29,edgeOk29⟩,restOk30⟩
lemma ndOk28 : nodeCheck nd28=true := by decide +kernel
lemma edgeOk28 : edgeCheck nd28 nd29=true := by decide +kernel
lemma restOk28 : chainCheck rest28=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk28,edgeOk28⟩,restOk29⟩
lemma ndOk27 : nodeCheck nd27=true := by decide +kernel
lemma edgeOk27 : edgeCheck nd27 nd28=true := by decide +kernel
lemma restOk27 : chainCheck rest27=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk27,edgeOk27⟩,restOk28⟩
lemma ndOk26 : nodeCheck nd26=true := by decide +kernel
lemma edgeOk26 : edgeCheck nd26 nd27=true := by decide +kernel
lemma restOk26 : chainCheck rest26=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk26,edgeOk26⟩,restOk27⟩
lemma ndOk25 : nodeCheck nd25=true := by decide +kernel
lemma edgeOk25 : edgeCheck nd25 nd26=true := by decide +kernel
lemma restOk25 : chainCheck rest25=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk25,edgeOk25⟩,restOk26⟩
lemma ndOk24 : nodeCheck nd24=true := by decide +kernel
lemma edgeOk24 : edgeCheck nd24 nd25=true := by decide +kernel
lemma restOk24 : chainCheck rest24=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk24,edgeOk24⟩,restOk25⟩
lemma ndOk23 : nodeCheck nd23=true := by decide +kernel
lemma edgeOk23 : edgeCheck nd23 nd24=true := by decide +kernel
lemma restOk23 : chainCheck rest23=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk23,edgeOk23⟩,restOk24⟩
lemma ndOk22 : nodeCheck nd22=true := by decide +kernel
lemma edgeOk22 : edgeCheck nd22 nd23=true := by decide +kernel
lemma restOk22 : chainCheck rest22=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk22,edgeOk22⟩,restOk23⟩
lemma ndOk21 : nodeCheck nd21=true := by decide +kernel
lemma edgeOk21 : edgeCheck nd21 nd22=true := by decide +kernel
lemma restOk21 : chainCheck rest21=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk21,edgeOk21⟩,restOk22⟩
lemma ndOk20 : nodeCheck nd20=true := by decide +kernel
lemma edgeOk20 : edgeCheck nd20 nd21=true := by decide +kernel
lemma restOk20 : chainCheck rest20=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk20,edgeOk20⟩,restOk21⟩
lemma ndOk19 : nodeCheck nd19=true := by decide +kernel
lemma edgeOk19 : edgeCheck nd19 nd20=true := by decide +kernel
lemma restOk19 : chainCheck rest19=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk19,edgeOk19⟩,restOk20⟩
lemma ndOk18 : nodeCheck nd18=true := by decide +kernel
lemma edgeOk18 : edgeCheck nd18 nd19=true := by decide +kernel
lemma restOk18 : chainCheck rest18=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk18,edgeOk18⟩,restOk19⟩
lemma ndOk17 : nodeCheck nd17=true := by decide +kernel
lemma edgeOk17 : edgeCheck nd17 nd18=true := by decide +kernel
lemma restOk17 : chainCheck rest17=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk17,edgeOk17⟩,restOk18⟩
lemma ndOk16 : nodeCheck nd16=true := by decide +kernel
lemma edgeOk16 : edgeCheck nd16 nd17=true := by decide +kernel
lemma restOk16 : chainCheck rest16=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk16,edgeOk16⟩,restOk17⟩
lemma ndOk15 : nodeCheck nd15=true := by decide +kernel
lemma edgeOk15 : edgeCheck nd15 nd16=true := by decide +kernel
lemma restOk15 : chainCheck rest15=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk15,edgeOk15⟩,restOk16⟩
lemma ndOk14 : nodeCheck nd14=true := by decide +kernel
lemma edgeOk14 : edgeCheck nd14 nd15=true := by decide +kernel
lemma restOk14 : chainCheck rest14=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk14,edgeOk14⟩,restOk15⟩
lemma ndOk13 : nodeCheck nd13=true := by decide +kernel
lemma edgeOk13 : edgeCheck nd13 nd14=true := by decide +kernel
lemma restOk13 : chainCheck rest13=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk13,edgeOk13⟩,restOk14⟩
lemma ndOk12 : nodeCheck nd12=true := by decide +kernel
lemma edgeOk12 : edgeCheck nd12 nd13=true := by decide +kernel
lemma restOk12 : chainCheck rest12=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk12,edgeOk12⟩,restOk13⟩
lemma ndOk11 : nodeCheck nd11=true := by decide +kernel
lemma edgeOk11 : edgeCheck nd11 nd12=true := by decide +kernel
lemma restOk11 : chainCheck rest11=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk11,edgeOk11⟩,restOk12⟩
lemma ndOk10 : nodeCheck nd10=true := by decide +kernel
lemma edgeOk10 : edgeCheck nd10 nd11=true := by decide +kernel
lemma restOk10 : chainCheck rest10=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk10,edgeOk10⟩,restOk11⟩
lemma ndOk9 : nodeCheck nd9=true := by decide +kernel
lemma edgeOk9 : edgeCheck nd9 nd10=true := by decide +kernel
lemma restOk9 : chainCheck rest9=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk9,edgeOk9⟩,restOk10⟩
lemma ndOk8 : nodeCheck nd8=true := by decide +kernel
lemma edgeOk8 : edgeCheck nd8 nd9=true := by decide +kernel
lemma restOk8 : chainCheck rest8=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk8,edgeOk8⟩,restOk9⟩
lemma ndOk7 : nodeCheck nd7=true := by decide +kernel
lemma edgeOk7 : edgeCheck nd7 nd8=true := by decide +kernel
lemma restOk7 : chainCheck rest7=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk7,edgeOk7⟩,restOk8⟩
lemma ndOk6 : nodeCheck nd6=true := by decide +kernel
lemma edgeOk6 : edgeCheck nd6 nd7=true := by decide +kernel
lemma restOk6 : chainCheck rest6=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk6,edgeOk6⟩,restOk7⟩
lemma ndOk5 : nodeCheck nd5=true := by decide +kernel
lemma edgeOk5 : edgeCheck nd5 nd6=true := by decide +kernel
lemma restOk5 : chainCheck rest5=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk5,edgeOk5⟩,restOk6⟩
lemma ndOk4 : nodeCheck nd4=true := by decide +kernel
lemma edgeOk4 : edgeCheck nd4 nd5=true := by decide +kernel
lemma restOk4 : chainCheck rest4=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk4,edgeOk4⟩,restOk5⟩
lemma ndOk3 : nodeCheck nd3=true := by decide +kernel
lemma edgeOk3 : edgeCheck nd3 nd4=true := by decide +kernel
lemma restOk3 : chainCheck rest3=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk3,edgeOk3⟩,restOk4⟩
lemma ndOk2 : nodeCheck nd2=true := by decide +kernel
lemma edgeOk2 : edgeCheck nd2 nd3=true := by decide +kernel
lemma restOk2 : chainCheck rest2=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk2,edgeOk2⟩,restOk3⟩
lemma ndOk1 : nodeCheck nd1=true := by decide +kernel
lemma edgeOk1 : edgeCheck nd1 nd2=true := by decide +kernel
lemma restOk1 : chainCheck rest1=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk1,edgeOk1⟩,restOk2⟩
lemma ndOk0 : nodeCheck nd0=true := by decide +kernel
lemma edgeOk0 : edgeCheck nd0 nd1=true := by decide +kernel
lemma restOk0 : chainCheck rest0=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨ndOk0,edgeOk0⟩,restOk1⟩
lemma gridCheck : chainCheck nodes=true := restOk0

end GrothendieckLB.DualQuadrature

open GrothendieckLB.DualQuadrature

theorem solution : start nodes = true ∧ chainCheck nodes = true := ⟨by decide +kernel, gridCheck⟩
